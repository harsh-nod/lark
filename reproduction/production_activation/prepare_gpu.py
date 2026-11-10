"""Prepare finite CPU references and an extracted upstream scalar comparison."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import shutil
import struct
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


def evaluate(n, inputs):
    a = n.args
    if n.op == "input":
        return inputs[a[0]][a[1]]
    if n.op == "lit":
        return f32(a[0] / a[1])
    if n.op == "un":
        x = evaluate(a[1], inputs)
        return {
            "fromHalf": lambda: x,
            "toHalf": lambda: struct.unpack("<e", struct.pack("<e", x))[0],
            "exp": lambda: f32(math.exp(x)),
        }[a[0]]()
    op, x, y = a
    x, y = evaluate(x, inputs), evaluate(y, inputs)
    return f32(
        {"add": lambda: x + y, "sub": lambda: x - y, "mul": lambda: x * y, "div": lambda: x / y}[
            op
        ]()
    )


def upstream_scalar(source):
    """Extract byte-identical helpers/loop from one pinned source revision.

    The new kernel header selects the scalar branch. Replacing the cache-load
    macro and removing the unselected packed branch are recorded rewrites;
    this is not a certificate for the original complete translation unit.
    """
    compute = source[
        source.index("template <typename scalar_t, scalar_t (*ACT_FN)") : source.index(
            "template <typename packed_t,\n"
        )
    ]
    silu_start = source.index("template <typename T>\n__device__ __forceinline__ T silu_kernel")
    silu = source[silu_start : source.index("template <typename packed_t>\n", silu_start)]
    kernel_start = source.index("// Activation and gating kernel template.")
    kernel_end = source.index("  if constexpr (use_vec)", kernel_start)
    header = source[kernel_start:kernel_end].replace("act_and_mul_kernel(", "original_scalar(")
    loop_start = source.index(
        "    for (int64_t idx = threadIdx.x; idx < d; idx += blockDim.x)", kernel_end
    )
    begin = source.index("{", loop_start)
    depth, end = 1, begin + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    loop = source[loop_start:end]
    return (
        "// Extracted from pinned vLLM source; see provenance.json and Apache-2.0 LICENSE.\n"
        "#define VLLM_LDG(ptr) (*(ptr))\nnamespace vllm_original {\n"
        + compute
        + silu
        + header
        + loop
        + "\n}\n}\n#undef VLLM_LDG\n"
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cpu", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    report = json.loads((args.cpu / "results.json").read_text())
    if report["status"] != "passed" or not all(x["rechecked"] for x in report["baselines"]):
        raise ValueError("Completed, rechecked CPU study required")
    certificate = args.cpu / "hip/certificate"
    proof = json.loads((certificate / "report.json").read_text())
    if proof["status"] != "verified":
        raise ValueError("Positive HIP certificate required")
    for name in ("kernel.cu", "reference.py", "task.json", "Main.lean", "report.json"):
        shutil.copyfile(certificate / name, args.output / name)
    provenance = json.loads((HERE / "provenance.json").read_text())
    upstream = HERE / "upstream/activation_kernels.cu"
    if sha(upstream) != provenance["source_sha256"]:
        raise ValueError("Pinned upstream source differs")
    shutil.copyfile(upstream, args.output / "upstream_activation_kernels.cu")
    shutil.copyfile(HERE / "provenance.json", args.output / "provenance.json")
    shutil.copyfile(HERE / "upstream/LICENSE", args.output / "LICENSE")
    shutil.copyfile(HERE / "upstream/PYTORCH_LICENSE", args.output / "PYTORCH_LICENSE")
    shutil.copytree(HERE / "upstream/torch_headers", args.output / "torch_headers")
    (args.output / "upstream_scalar.cuh").write_text(upstream_scalar(upstream.read_text()))
    driver = """#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <cmath>
#include <cstdint>
#include <torch/headeronly/util/Half.h>
#include "kernel.cu"
#include "upstream_scalar.cuh"
using OriginalHalf = torch::headeronly::Half;
static_assert(sizeof(OriginalHalf) == 2 && alignof(OriginalHalf) == 2);
extern "C" int run_case(void* a, void* b, void* c) {
  hipLaunchKernelGGL(vllm_silu_and_mul_adapted, dim3(2), dim3(5), 0, 0,
    (__half*)a, (const __half*)b);
  hipError_t e = hipGetLastError();
  if (e != hipSuccess) return (int)e;
  hipLaunchKernelGGL((vllm_original::original_scalar<OriginalHalf, __half2,
    vllm_original::silu_kernel<OriginalHalf>, nullptr, true, false, false, false>),
    dim3(2), dim3(5), 0, 0, (OriginalHalf*)c, (const OriginalHalf*)b, 5, 0.0f, 1.0f, 0.0f);
  return (int)hipGetLastError();
}
"""
    (args.output / "driver.hip").write_text(driver)
    import torch

    torch.set_num_threads(1)
    task = Task.read(certificate / "task.json")
    spec = read_spec((certificate / "reference.py").read_text(), task)
    env = {}
    exec(compile((certificate / "reference.py").read_text(), "reference.py", "exec"), env)
    rng = random.Random(261102028)
    trials, witness = [], None
    ast_max_error, ast_comparisons, rounding_differences = 0.0, 0, 0
    for trial in range(1024):
        values = (
            [0.0] * 20
            if trial == 0
            else [1.0] * 20
            if trial == 1
            else [-1.0] * 20
            if trial == 2
            else [(-1.0 if i % 2 else 1.0) for i in range(20)]
            if trial == 3
            else [rng.randint(-2048, 2048) / 256 for _ in range(20)]
        )
        x = torch.tensor(values, dtype=torch.float16).reshape(2, 10)
        expected = env["reference"](x).flatten().tolist()
        ast_values = [evaluate(n, {1: values}) for n in spec]
        for a, b in zip(ast_values, expected):
            ast_comparisons += 1
            ast_max_error = max(ast_max_error, abs(a - b))
            if abs(a - b) > 0.002 + 0.002 * abs(b):
                raise ValueError("Independent AST/CPU reference mismatch")
        packed = x.reshape(2, 2, 5).float()
        g, u = packed.select(1, 0), packed.select(1, 1)
        naive = ((g / (1 + torch.exp(-g))) * u).half().flatten().tolist()
        different = sum(a != b for a, b in zip(expected, naive))
        rounding_differences += different
        if different and witness is None:
            witness = {
                "trial": trial,
                "input": values,
                "rounded_before_multiply": expected,
                "without_intermediate_rounding": naive,
            }
        trials.append({"input": values, "expected": expected})
    if witness is None:
        raise ValueError("Missing finite witness for the intermediate-rounding control")
    dataset = {
        "schema": 1,
        "trials": trials,
        "torch": torch.__version__,
        "ast_comparisons": ast_comparisons,
        "ast_max_abs_error": ast_max_error,
        "intermediate_rounding_differences": rounding_differences,
        "rounding_witness": witness,
        "atol": 0.002,
        "rtol": 0.002,
        "certificate_report_sha256": sha(certificate / "report.json"),
        "scope": report["scope"],
    }
    (args.output / "dataset.json").write_text(json.dumps(dataset, indent=2) + "\n")
    manifest = {
        "files": {
            str(p.relative_to(args.output)): sha(p)
            for p in sorted(args.output.rglob("*"))
            if p.is_file()
        },
        "generator_sha256": sha(Path(__file__)),
        "trials": 1024,
        "output_comparisons_per_method": 10240,
        "original_paper_fully_reproduced": False,
        "model_calls": 0,
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "prepared",
                "trials": 1024,
                "ast_comparisons": ast_comparisons,
                "rounding_differences": rounding_differences,
            }
        )
    )


if __name__ == "__main__":
    main()
