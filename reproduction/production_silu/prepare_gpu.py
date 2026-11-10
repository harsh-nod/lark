"""Build binary CPU references and exact-source/upstream GPU comparison inputs."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import silu  # noqa: E402
from reproduction.production_activation.prepare_gpu import upstream_scalar  # noqa: E402

HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cpu", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    cpu = args.cpu.resolve()
    for name, expected in json.loads((cpu / "manifest.json").read_text()).items():
        if sha(cpu / name) != expected:
            raise ValueError("CPU evidence differs: " + name)
    study = json.loads((cpu / "results.json").read_text())
    if study["status"] != "passed" or len(study["baselines"]) != 8:
        raise ValueError("Complete CPU study required")
    args.output.mkdir(parents=True, exist_ok=False)
    out = args.output
    legacy = ROOT / "reproduction/production_activation"
    provenance = json.loads((HERE / "provenance.json").read_text())
    upstream = legacy / "upstream/activation_kernels.cu"
    if sha(upstream) != provenance["source_sha256"]:
        raise ValueError("Pinned vLLM source differs")
    shutil.copyfile(upstream, out / "upstream_activation_kernels.cu")
    shutil.copyfile(HERE / "provenance.json", out / "provenance.json")
    for name in ("LICENSE", "PYTORCH_LICENSE"):
        shutil.copyfile(legacy / "upstream" / name, out / name)
    shutil.copytree(legacy / "upstream/torch_headers", out / "torch_headers")
    (out / "upstream_scalar.cuh").write_text(upstream_scalar(upstream.read_text()))
    driver = """#include <hip/hip_runtime.h>
#include <hip/hip_fp16.h>
#include <torch/headeronly/util/Half.h>
#include <cmath>
#include <cstdint>
#include "upstream_scalar.cuh"
using OriginalHalf = torch::headeronly::Half;
static_assert(sizeof(OriginalHalf) == 2 && alignof(OriginalHalf) == 2);
"""
    import numpy
    import torch

    torch.set_num_threads(1)
    metadata = {
        "schema": 1,
        "torch": torch.__version__,
        "numpy": numpy.__version__,
        "seed": 261102028,
        "atol": 0.002,
        "rtol": 0.002,
        "trials_per_case": 10,
        "cases": [],
        "ast_comparisons": 0,
        "ast_bit_differences": 0,
        "rounding_differences": 0,
        "scope": study["scope"],
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
    }
    input_offset = output_offset = 0
    for case_id, case in enumerate(sorted((HERE / "cases").iterdir())):
        key = case.name
        cert = cpu / (key + "-hip/certificate")
        report = json.loads((cert / "report.json").read_text())
        if report["status"] != "verified" or report["model_profile"] != silu.PROFILE:
            raise ValueError("Verified multiwave certificate required")
        for name, digest in report["files"].items():
            if sha(cert / name) != digest:
                raise ValueError("Certificate file differs: " + name)
        for name in ("kernel.cu", "reference.py", "task.json", "Main.lean", "report.json"):
            shutil.copyfile(cert / name, out / (key + "-" + name))
        task, tr, ref = silu.prepare(
            *(
                (cert / n).read_bytes().decode("utf-8")
                for n in ("kernel.cu", "reference.py", "task.json")
            )
        )
        rows, width = task.buffers[0].shape
        if len(tr.program) != 10:
            raise ValueError("Unexpected instruction count")
        env = {}
        source = (cert / "reference.py").read_text()
        exec(compile(source, str(cert / "reference.py"), "exec"), env)
        n_input, n_output = rows * 2 * width, rows * width
        entry = {
            "id": case_id,
            "key": key,
            "rows": rows,
            "hidden": width,
            "grid": task.grid,
            "block": task.block,
            "warp": task.warp,
            "entry": task.entry,
            "input_elements": n_input,
            "output_elements": n_output,
            "input_offset_bytes": input_offset,
            "output_offset_bytes": output_offset,
            "trials": 10,
            "source_sha256": sha(cert / "kernel.cu"),
            "reference_sha256": sha(cert / "reference.py"),
            "task_sha256": sha(cert / "task.json"),
            "theorem_sha256": sha(cert / "Main.lean"),
            "report_sha256": sha(cert / "report.json"),
        }
        rng = torch.Generator().manual_seed(261102028 + case_id * 100)
        counter = torch.arange(n_input, dtype=torch.int64)
        for trial in range(10):
            if trial < 6:
                values = (torch.randn(n_input, generator=rng) * 0.25).half()
            elif trial == 6:
                values = torch.zeros(n_input, dtype=torch.float16)
            elif trial == 7:
                values = torch.full((n_input,), 0.125, dtype=torch.float16)
            elif trial == 8:
                values = (((counter * 17 + 1) % 67).float() - 33).div(16).half()
            else:
                corners = torch.tensor(
                    [-8, -1, -0.0, 0.0, 2**-24, 0.33325, 0.9995, 1, 8, 5.996], dtype=torch.float16
                )
                values = corners[(counter + counter // 13) % len(corners)]
            packed = values.reshape(rows, 2, width)
            x, y = packed.select(1, 0), packed.select(1, 1)
            expected = env["reference"](values.reshape(rows, 2 * width)).contiguous()

            def evaluate(expr):
                if expr.op == "input":
                    return (
                        x if expr.args == (1, 0) else y if expr.args == (1, 1) else invalid_leaf()
                    )
                if expr.op == "lit":
                    return expr.args[0] / expr.args[1]
                if expr.op == "un":
                    value = evaluate(expr.args[1])
                    return {
                        "fromHalf": lambda: value.float(),
                        "toHalf": lambda: value.half(),
                        "exp": lambda: torch.exp(value),
                    }[expr.args[0]]()
                if expr.op == "bin":
                    op, a, b = expr.args
                    a, b = evaluate(a), evaluate(b)
                    return {
                        "add": lambda: a + b,
                        "sub": lambda: a - b,
                        "mul": lambda: a * b,
                        "div": lambda: a / b,
                    }[op]()
                raise ValueError("Unexpected AST node")

            def invalid_leaf():
                raise ValueError("Unexpected symbolic reference leaf")

            ast_result = evaluate(ref).contiguous()
            mismatch = (ast_result.view(torch.int16) != expected.view(torch.int16)).sum().item()
            metadata["ast_comparisons"] += n_output
            metadata["ast_bit_differences"] += mismatch
            if mismatch:
                raise ValueError("AST and original CPU reference differ")
            gate, up = x.float(), y.float()
            naive = ((gate / (1.0 + torch.exp((0.0 - gate) * 1.0))) * (up + 0.0)).half()
            metadata["rounding_differences"] += (
                (naive.view(torch.int16) != expected.view(torch.int16)).sum().item()
            )
            with (out / "input.bin").open("ab") as f:
                f.write(values.contiguous().numpy().tobytes())
            with (out / "expected.bin").open("ab") as f:
                f.write(expected.numpy().tobytes())
        metadata["cases"].append(entry)
        input_offset += n_input * 2 * 10
        output_offset += n_output * 2 * 10
        driver += f'#include "{key}-kernel.cu"\n'
    driver += 'extern "C" int run_case(int id, void* a, void* b, void* c) {\n switch (id) {\n'
    for case in metadata["cases"]:
        driver += f"""case {case["id"]}: {{
  hipLaunchKernelGGL({case["entry"]}, dim3({case["grid"]}), dim3({case["block"]}), 0, 0,
    (__half*)a, (const __half*)b);
  hipError_t e = hipGetLastError(); if (e != hipSuccess) return (int)e;
  hipLaunchKernelGGL((vllm_original::original_scalar<OriginalHalf, __half2,
    vllm_original::silu_kernel<OriginalHalf>, nullptr, true, false, false, false>),
    dim3({case["grid"]}), dim3({case["block"]}), 0, 0, (OriginalHalf*)c,
    (const OriginalHalf*)b, {case["hidden"]}, 0.0f, 1.0f, 0.0f); break;
}}
"""
    driver += "default: return -1; } return (int)hipGetLastError(); }\n"
    driver += """extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p; if (hipGetDeviceProperties(&p, 0) != hipSuccess) return -1;
  return which == 0 ? p.warpSize : which == 1 ? p.maxThreadsPerBlock : -1;
}
"""
    (out / "driver.hip").write_text(driver)
    (out / "dataset.json").write_text(json.dumps(metadata, indent=2) + "\n")
    manifest = {
        "files": {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
        "generator_sha256": sha(Path(__file__)),
        "original_paper_fully_reproduced": False,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "prepared",
                "trials": 30,
                "outputs_per_method": output_offset // 2,
                "ast_comparisons": metadata["ast_comparisons"],
                "rounding_differences": metadata["rounding_differences"],
            }
        )
    )


if __name__ == "__main__":
    main()
