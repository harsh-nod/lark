#!/usr/bin/env python3
"""Run independent HIP numerical/latency experiments at the paper's shapes."""

from __future__ import annotations

import argparse
import ctypes
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import statistics
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from reproduction.catalog import CONTRACTS, NAMES, PAPER_HIP_US, SHAPES, reference


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def timer(fn, torch, repeats, rounds=7):
    for _ in range(5):
        fn()
    torch.cuda.synchronize()
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        for _ in range(repeats):
            result = fn()
    graph.replay()
    torch.cuda.synchronize()
    samples = []
    for _ in range(rounds):
        start, end = torch.cuda.Event(enable_timing=True), torch.cuda.Event(enable_timing=True)
        start.record()
        graph.replay()
        end.record()
        end.synchronize()
        samples.append(start.elapsed_time(end) * 1000 / repeats)
    # Keep the captured output live until all graph replays have completed.
    del result
    return {
        "median_us": statistics.median(samples),
        "rounds_us": samples,
        "method": "HIP-event timing of one captured graph containing repeated calls",
        "calls_per_graph": repeats,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cases", nargs="+", choices=NAMES, default=list(NAMES))
    parser.add_argument("--trials", type=int, default=6)
    parser.add_argument("--repeats", type=int, default=20)
    parser.add_argument("--torch-compile", action="store_true")
    parser.add_argument(
        "--calibration", type=Path, help="JSON operand pairs and expected Float64 Lean results"
    )
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output must be a new directory")
    args.output.mkdir(parents=True)
    import torch

    if not torch.cuda.is_available() or not torch.version.hip:
        parser.error("a working ROCm PyTorch installation and AMD GPU are required")
    torch.set_grad_enabled(False)
    torch.backends.cuda.matmul.allow_tf32 = False
    source = Path(__file__).parent / "hip" / "kernels.hip"
    library = args.output / "kernels.so"
    arch = torch.cuda.get_device_properties(0).gcnArchName.split(":")[0]
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-shared",
        "-fPIC",
        "-ffp-contract=off",
        "--offload-arch=" + arch,
        str(source),
        "-o",
        str(library),
    ]
    started = time.time()
    built = subprocess.run(command, text=True, capture_output=True)
    (args.output / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    lib = ctypes.CDLL(str(library.resolve()))
    lib.lark_launch.argtypes = [
        ctypes.c_int,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.c_void_p,
        ctypes.c_void_p,
        ctypes.c_void_p,
    ]
    lib.lark_launch.restype = ctypes.c_int
    report = {
        "schema": 1,
        "experiment": "independent-hip-functional-and-latency-reimplementation",
        "paper": "https://arxiv.org/abs/2611.02028v1",
        "paper_section": "A.4.10, Table 9, Table 14",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": torch.cuda.get_device_name(0),
        "architecture": arch,
        "torch": torch.__version__,
        "torch_hip": torch.version.hip,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "python": sys.version.split()[0],
        "kernel_sha256": sha(source),
        "runner_sha256": sha(Path(__file__)),
        "catalog_sha256": sha(Path(__file__).parent / "catalog.py"),
        "compile_flags": command[1:-3],
        "build_seconds": time.time() - started,
        "rtol": 0.01,
        "atol": 0.01,
        "seed": 261102028,
        "limitations": [
            "Original kernels/registry unavailable; no original-kernel latency reproduction",
            "Independent FP16 HIP kernels at Table 9 dimensions; mathematical contracts are declared per task",
            "FP32 arithmetic and FP16 storage; all numerical results are separate from Lean proofs",
            "L2 ports are AMD extensions; the paper reports L2 only on PTX/H100",
            "No fastest-vendor-library sweep; eager references include precision-conversion costs",
            "Compile baseline uses max-autotune-no-cudagraphs to allow the same external timing graph",
        ],
        "cases": [],
    }
    for name in args.cases:
        index = NAMES.index(name)
        shapes, output_shape = SHAPES[name]
        row = {
            "task": name,
            "contract": CONTRACTS[name],
            "input_shapes": shapes,
            "output_shape": output_shape,
            "dtype": "float16",
            "formal_certificate_for_this_program": False,
            "paper_hip_us": PAPER_HIP_US[index] if index < 12 else None,
        }
        torch.manual_seed(report["seed"] + index)
        tensors = [torch.empty(s, device="cuda", dtype=torch.float16) for s in shapes]
        output = torch.empty(output_shape, device="cuda", dtype=torch.float16)
        scratch = torch.empty((64, 1024), device="cuda", dtype=torch.float16)
        pointers = (ctypes.c_void_p * len(tensors))(*[x.data_ptr() for x in tensors])

        def launch():
            code = lib.lark_launch(
                index,
                pointers,
                output.data_ptr(),
                scratch.data_ptr(),
                torch.cuda.current_stream().cuda_stream,
            )
            if code:
                raise RuntimeError(f"HIP launch error {code}")
            return output

        def ref():
            return reference(name, tensors)

        try:
            checks = []
            for trial in range(args.trials + 4):
                for tensor in tensors:
                    if trial < args.trials:
                        tensor.normal_(0, 0.25)
                    elif trial == args.trials:
                        tensor.zero_()
                    elif trial == args.trials + 1:
                        tensor.fill_(0.125)
                    elif trial == args.trials + 2:
                        tensor.copy_(
                            ((torch.arange(tensor.numel(), device="cuda") % 2) * 2 - 1).reshape(
                                tensor.shape
                            )
                            * 0.125
                        )
                    else:
                        tensor.uniform_(-0.001, 0.001)
                expected = ref()
                launch()
                torch.cuda.synchronize()
                torch.testing.assert_close(
                    output, expected, rtol=report["rtol"], atol=report["atol"]
                )
                checks.append(
                    {
                        "trial": trial,
                        "max_abs_error": (output.float() - expected.float()).abs().max().item(),
                        "finite": bool(torch.isfinite(output).all()),
                    }
                )
            # Time representative random data, rather than the final near-zero probe.
            for tensor in tensors:
                tensor.normal_(0, 0.25)
            row.update(status="passed", numerical_checks=checks)
            row["hip"] = timer(launch, torch, args.repeats)
            row["torch_eager"] = timer(ref, torch, args.repeats)
            row["eager_speedup"] = row["torch_eager"]["median_us"] / row["hip"]["median_us"]
            if args.torch_compile:
                try:
                    # Give each workload its own specialization without exhausting
                    # Dynamo's recompile limit for this closure's code object.
                    torch.compiler.reset()
                    compiled = torch.compile(ref, fullgraph=True, mode="max-autotune-no-cudagraphs")
                    expected = ref()
                    actual = compiled()
                    torch.cuda.synchronize()
                    torch.testing.assert_close(actual, expected, rtol=0.01, atol=0.01)
                    row["torch_compile"] = timer(compiled, torch, args.repeats)
                except Exception as e:
                    row["torch_compile"] = {"status": "failed", "error": str(e)}
        except Exception as e:
            row.update(status="failed", error=str(e))
        report["cases"].append(row)
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(name, row["status"], row.get("hip", {}).get("median_us"), flush=True)
    if args.calibration:
        data = json.loads(args.calibration.read_text())
        n = len(data["a"])
        a = torch.tensor(data["a"], device="cuda", dtype=torch.float32)
        b = torch.tensor(data["b"], device="cuda", dtype=torch.float32)
        output = torch.empty((4, n), device="cuda", dtype=torch.float32)
        lib.lark_scalar.argtypes = [
            ctypes.c_void_p,
            ctypes.c_void_p,
            ctypes.c_void_p,
            ctypes.c_int,
            ctypes.c_void_p,
        ]
        status = lib.lark_scalar(
            a.data_ptr(),
            b.data_ptr(),
            output.data_ptr(),
            n,
            torch.cuda.current_stream().cuda_stream,
        )
        if status:
            raise RuntimeError(status)
        torch.cuda.synchronize()
        expected = torch.tensor(data["lean_results"], dtype=torch.float32)
        actual = output.cpu()
        mismatches = (actual != expected) & ~((actual == 0) & (expected == 0))
        report["scalar_calibration"] = {
            "ops": ["add", "sub", "mul", "max"],
            "pairs": n,
            "comparison": "GPU FP32 vs rounded Lean Float64 evaluations on finite strata",
            "mismatches": int(mismatches.sum()),
            "operand_sha256": sha(args.calibration),
            "model_sha256": data["model_sha256"],
            "lean_source_sha256": data["lean_source_sha256"],
            "max_abs_error": float((actual - expected).abs().max()),
            "scope": "Finite samples of four scalar operations only; not a proof of hardware semantics",
        }
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print("scalar_calibration", report["scalar_calibration"], flush=True)
    failed = any(r["status"] != "passed" for r in report["cases"])
    failed |= report.get("scalar_calibration", {}).get("mismatches", 0) != 0
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
