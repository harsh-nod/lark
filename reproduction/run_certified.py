#!/usr/bin/env python3
"""Numerically run the exact float32 HIP sources used in reduced certificates."""

import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
NAMES = (
    "relu",
    "gemv",
    "gemm",
    "batchmatmul",
    "linear",
    "conv2d",
    "depthwise_conv",
    "barrier_sum",
    "llmc_fixed",
)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--certificate-index", required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    import torch

    if not torch.version.hip or not torch.cuda.is_available():
        raise RuntimeError("ROCm GPU required")
    index = json.loads(args.certificate_index.read_text())
    tasks = []
    source = "#include <hip/hip_runtime.h>\n#include <cmath>\n"
    for name in NAMES:
        case = ROOT / "cases" / name
        task = json.loads((case / "task.json").read_text())
        if sha(case / "kernel.hip") != index[name]["source_sha256"]:
            raise RuntimeError("proof/source mismatch: " + name)
        if sha(case / "reference.py") != index[name]["reference_sha256"]:
            raise RuntimeError("proof/reference mismatch: " + name)
        if sha(case / "task.json") != index[name]["task_sha256"]:
            raise RuntimeError("proof/task mismatch: " + name)
        if index[name]["status"] != "verified":
            raise RuntimeError("certificate was not verified: " + name)
        source += (case / "kernel.hip").read_text() + "\n"
        tasks.append(task)
    source += 'extern "C" int run_small(int id,void** a,void* stream) {\n switch(id) {\n'
    for id, task in enumerate(tasks):
        parameters = ", ".join(
            f"({'const ' if b['role'] == 'input' else ''}float*)a[{j}]"
            for j, b in enumerate(task["buffers"])
        )
        source += f"case {id}: hipLaunchKernelGGL({task['entry']},dim3({task['launch']['grid']}),dim3({task['launch']['block']}),0,(hipStream_t)stream,{parameters}); break;\n"
    source += "default:return -1; } return int(hipGetLastError()); }\n"
    src = args.output / "certified.hip"
    src.write_text(source)
    libpath = args.output / "certified.so"
    arch = torch.cuda.get_device_properties(0).gcnArchName.split(":")[0]
    build = subprocess.run(
        [
            "hipcc",
            "-O3",
            "-shared",
            "-fPIC",
            "-ffp-contract=off",
            "--offload-arch=" + arch,
            str(src),
            "-o",
            str(libpath),
        ],
        capture_output=True,
        text=True,
    )
    (args.output / "build.log").write_text(build.stdout + build.stderr)
    if build.returncode:
        raise RuntimeError(build.stderr)
    lib = ctypes.CDLL(str(libpath.resolve()))
    lib.run_small.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_void_p), ctypes.c_void_p]
    report = {
        "schema": 1,
        "experiment": "exact-certified-source-hip-numerical-checks",
        "device": torch.cuda.get_device_name(0),
        "architecture": arch,
        "torch": torch.__version__,
        "cases": [],
        "wrapper_sha256": sha(src),
        "runner_sha256": sha(Path(__file__)),
        "note": "Only the fixed/reduced kernels are executed. The deliberately racy source is tested symbolically on CPU.",
    }
    for id, (name, task) in enumerate(zip(NAMES, tasks)):
        case = ROOT / "cases" / name
        env = {}
        exec(compile((case / "reference.py").read_text(), str(case / "reference.py"), "exec"), env)
        row = {
            "task": name,
            "certificate": index[name],
            "source_sha256": sha(case / "kernel.hip"),
            "reference_sha256": sha(case / "reference.py"),
            "trials": [],
            "dtype": "float32",
        }
        try:
            for seed in range(10):
                torch.manual_seed(261102028 + seed)
                tensors = []
                inputs = []
                for b in task["buffers"]:
                    if b["role"] == "input":
                        tensor = torch.randint(-8, 9, b["shape"], device="cuda").float() / 4
                        inputs.append(tensor)
                    else:
                        tensor = torch.full(b["shape"], float("nan"), device="cuda")
                    tensors.append(tensor)
                expected = env["reference"](*inputs)
                expected = (expected,) if not isinstance(expected, tuple) else expected
                saved = [x.clone() for x in inputs]
                pointers = (ctypes.c_void_p * len(tensors))(*[x.data_ptr() for x in tensors])
                code = lib.run_small(id, pointers, torch.cuda.current_stream().cuda_stream)
                if code:
                    raise RuntimeError(f"HIP error {code}")
                torch.cuda.synchronize()
                outputs = [x for x, b in zip(tensors, task["buffers"]) if b["role"] == "output"]
                for a, b in zip(outputs, expected):
                    torch.testing.assert_close(a, b, rtol=0, atol=0)
                for a, b in zip(inputs, saved):
                    torch.testing.assert_close(a, b, rtol=0, atol=0)
                row["trials"].append({"seed": seed, "exact_agreement": True})
            row["status"] = "passed"
        except Exception as e:
            row.update(status="failed", error=str(e))
        report["cases"].append(row)
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(name, row["status"], flush=True)
    return int(any(x["status"] != "passed" for x in report["cases"]))


if __name__ == "__main__":
    raise SystemExit(main())
