"""Prepare finite native RMSNorm comparisons; no whole-kernel proof is claimed."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rmsnorm, partition_collective  # noqa: E402

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract_function(source, marker):
    start = source.index(marker)
    body = source.index("{", start)
    depth, end = 1, body + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]


def upstream_context():
    source = (HERE / "upstream/layernorm_kernels.cu").read_text()
    vector = (HERE / "upstream/csrc/quantization/vectorization.cuh").read_text()
    helper = (HERE / "upstream/csrc/quantization/vectorization_utils.cuh").read_text()
    parts = [
        extract_function(vector, "template <typename scalar_t, size_t vec_size>") + ";",
        extract_function(
            helper, "template <int VEC_SIZE, typename InT, typename VecOp, typename ScaOp>"
        ),
        extract_function(
            source, "template <typename scalar_t, int VEC_SIZE, int NUM_DIMS, bool HasWeight>"
        ),
    ]
    # Every selected definition is byte-identical; only unrelated translation-unit
    # context is omitted. The actual hipCUB/rocPRIM reduction is compiled unchanged.
    return "namespace vllm {\n" + "\n\n".join(parts) + "\n}\n", [
        hashlib.sha256(p.encode()).hexdigest() for p in parts
    ]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source_dir = HERE / "cases/weighted_16384"
    task = native_rmsnorm.parse_task((source_dir / "task.json").read_text())
    native_rmsnorm.check_reference((source_dir / "reference.py").read_text(), task)
    translation = partition_collective.translate((source_dir / "kernel.hip").read_text(), task)
    if len(translation.program) != 71:
        raise ValueError("Unexpected source IR")
    provenance = json.loads((HERE / "provenance.json").read_text())
    if sha(HERE / "upstream/layernorm_kernels.cu") != provenance["source_sha256"]:
        raise ValueError("Pinned vLLM source differs")
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(source_dir / name, out / name)
    for name in ("layernorm_kernels.cu", "LICENSE"):
        shutil.copyfile(HERE / "upstream" / name, out / name)
    shutil.copyfile(HERE / "upstream/csrc/cub_helpers.h", out / "cub_helpers.h")
    legacy = ROOT / "reproduction/production_activation/upstream"
    carrier = json.loads((legacy.parent / "provenance.json").read_text())[
        "comparison_scalar_carrier"
    ]
    for name, digest in carrier["header_sha256"].items():
        if sha(legacy / "torch_headers" / name) != digest:
            raise ValueError("Pinned PyTorch Half header differs")
    shutil.copytree(legacy / "torch_headers", out / "torch_headers")
    shutil.copyfile(legacy / "PYTORCH_LICENSE", out / "PYTORCH_LICENSE")
    context, definition_hashes = upstream_context()
    (out / "upstream_context.cuh").write_text(context)
    driver = """#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <torch/headeronly/util/Half.h>
#include <cmath>
#include <cstdint>
#include <type_traits>
#include "cub_helpers.h"
#include "upstream_context.cuh"
#include "kernel.hip"
using OriginalHalf = torch::headeronly::Half;
static_assert(sizeof(OriginalHalf) == 2 && alignof(OriginalHalf) == 2);
extern "C" int run_case(int rows, void* adapted, void* input, void* weight, void* upstream) {
  hipLaunchKernelGGL(rmsnorm, dim3(rows), dim3(1024), 0, 0,
    (__half*)adapted, (const __half*)input, (const __half*)weight);
  hipError_t e = hipGetLastError(); if (e != hipSuccess) return (int)e;
  hipLaunchKernelGGL((vllm::rms_norm_kernel<OriginalHalf, 8, 2, true>),
    dim3(rows), dim3(1024), 0, 0, (OriginalHalf*)upstream, (const OriginalHalf*)input,
    (int64_t)16384, (int64_t)0, (int64_t)0, (int64_t)rows, (int64_t)1,
    (const OriginalHalf*)weight, (int64_t)0, 0.00001f, rows, 16384);
  return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p; if (hipGetDeviceProperties(&p, 0) != hipSuccess) return -1;
  return which == 0 ? p.warpSize : which == 1 ? p.maxThreadsPerBlock : -1;
}
"""
    (out / "driver.hip").write_text(driver)
    import numpy as np
    import torch

    torch.set_num_threads(1)
    env = {}
    exec(compile((out / "reference.py").read_text(), "reference.py", "exec"), env)
    meta = {
        "schema": 1,
        "torch": torch.__version__,
        "torch_git_commit": torch.version.git_version,
        "numpy": np.__version__,
        "seed": 261102028,
        "atol": 0.002,
        "rtol": 0.002,
        "cases": [],
        "upstream_definition_sha256": definition_hashes,
        "comparison_scalar_carrier": carrier,
        "source_tree_cpu_bit_differences_from_torch": 0,
        "complete_source_proof": False,
        "certificates": 0,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": "Independent finite numerical comparison of a development adaptation and an extracted unchanged vLLM FP16 template/reader with installed native hipCUB. Not a whole-kernel Lean certificate, IEEE equivalence theorem, full upstream API validation or original paper experiment.",
    }
    offset = weight_offset = 0
    for rows in (1, 3, 64, 255):
        rng = torch.Generator().manual_seed(meta["seed"] + rows)
        count = rows * 16384
        counter = torch.arange(count, dtype=torch.int64)
        weight_counter = torch.arange(16384, dtype=torch.int64)
        case = {
            "rows": rows,
            "hidden": 16384,
            "grid": rows,
            "block": 1024,
            "warp": 64,
            "elements": count,
            "trials": [],
        }
        for trial in range(6):
            weight = (((weight_counter * 7) % 65).float() - 32).div(16).half()
            if trial == 0:
                x = (torch.randn(count, generator=rng) * 0.25).half()
                label = "seeded-normal"
            elif trial == 1:
                x = torch.zeros(count, dtype=torch.float16)
                label = "zero"
            elif trial == 2:
                x = torch.full((count,), 0.125, dtype=torch.float16)
                label = "constant"
            elif trial == 3:
                x = (((counter * 17 + 1) % 67).float() - 33).div(16).half()
                label = "structured-dyadic"
            elif trial == 4:
                corners = torch.tensor(
                    [-8, -1, -0.0, 0.0, 2**-24, 0.33325, 0.9995, 1, 8, 5.996], dtype=torch.float16
                )
                x = corners[(counter + counter // 13) % len(corners)]
                label = "half-corners"
            else:
                corners = torch.tensor(
                    [-65504, 65504, -(2**-24), 2**-24, -1, 1, 0, 0.001], dtype=torch.float16
                )
                x = corners[(counter * 19 + counter // 71) % len(corners)]
                label = "mixed-magnitudes"
            expected = env["reference"](x.reshape(rows, 16384), weight).contiguous()
            values = x.numpy().astype(np.float32).reshape(rows, 2, 1024, 8)
            partials = np.zeros((rows, 1024), dtype=np.float32)
            for iteration in range(2):
                for component in range(8):
                    v = values[:, iteration, :, component]
                    partials = partials + v * v
            partials = partials.reshape(rows, 16, 64)
            for _ in range(6):
                partials = partials[..., 0::2] + partials[..., 1::2]
            partials = partials[..., 0]
            for _ in range(4):
                partials = partials[:, 0::2] + partials[:, 1::2]
            scale = np.float32(1) / np.sqrt(partials[:, 0] / np.float32(16384) + np.float32(1e-5))
            tree = (
                x.numpy().astype(np.float32).reshape(rows, 16384)
                * scale[:, None]
                * weight.numpy().astype(np.float32)
            ).astype(np.float16)
            meta["source_tree_cpu_bit_differences_from_torch"] += int(
                np.count_nonzero(tree.view(np.uint16) != expected.numpy().view(np.uint16))
            )
            entry = {
                "trial": trial,
                "label": label,
                "offset_bytes": offset,
                "weight_offset_bytes": weight_offset,
            }
            for name, value in (
                ("input.bin", x.numpy()),
                ("weight.bin", weight.numpy()),
                ("expected.bin", expected.numpy()),
                ("source-tree.bin", tree),
            ):
                with (out / name).open("ab") as f:
                    f.write(value.tobytes())
            offset += count * 2
            weight_offset += 16384 * 2
            case["trials"].append(entry)
        meta["cases"].append(case)
        print(json.dumps({"prepared_rows": rows, "trials": 6}), flush=True)
    (out / "dataset.json").write_text(json.dumps(meta, indent=2) + "\n")
    manifest = {
        "files": {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
        "generator_sha256": sha(Path(__file__)),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "prepared",
                "trials": 24,
                "outputs_per_method": offset // 2,
                "source_tree_cpu_bit_differences_from_torch": meta[
                    "source_tree_cpu_bit_differences_from_torch"
                ],
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
