#!/usr/bin/env python3
"""Render the recorded experiment JSON as a reviewable Markdown report."""

import argparse
from collections import Counter
import json
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results", type=Path, default=ROOT / "results")
    p.add_argument("--output", type=Path, default=ROOT / "RESULTS.md")
    args = p.parse_args()

    def read(name):
        return json.loads((args.results / name).read_text())

    cpu = read("cpu.json")
    gpu = read("mi300x.json")
    certified = read("certified-hip.json")
    race = read("production-race/results.json")
    validation = read("validation.json")
    # Refuse to present an interrupted experiment as complete.
    assert len(cpu["formal"]) == 18
    assert len(cpu["mutations"]) == 28
    assert len(cpu["positive_controls"]) == 6
    assert len(cpu["grouping_ablation"]) == len(cpu["scaling"]) == 4
    assert len(gpu["cases"]) == 17 and len(certified["cases"]) == 9
    good = sum(r["status"] == "verified" and r["rechecked"] for r in cpu["formal"])
    outcomes = Counter(r["outcome"] for r in cpu["mutations"])
    positives = sum(r["accepted"] for r in cpu["positive_controls"])
    gpu_good = sum(r["status"] == "passed" for r in gpu["cases"])
    checks = sum(len(r.get("numerical_checks", [])) for r in gpu["cases"])
    exact = sum(len(r["trials"]) for r in certified["cases"] if r["status"] == "passed")
    calibration = gpu["scalar_calibration"]
    lines = [
        "# Recorded reproduction results",
        "",
        "Run date: 2026-11-09. [Methodology and commands](README.md). "
        "[Raw results and proof artifacts](results/).",
        "",
        "**Partial independent reproduction; no NVIDIA GPU or model calls were used.** "
        "CPU Lean certificates concern reduced float32 programs. The large FP16 HIP "
        "programs are independent numerical/performance experiments and are not certified.",
        "",
        "| Experiment | Observed | Coverage boundary |",
        "| --- | --- | --- |",
        f"| Reduced certificates | {good}/18 verified and rechecked | Seven L1 families × two languages, plus sum proxy and minimal repair × two languages |",
        f"| Mutations sent directly to Lean | {outcomes['unproved']}/28 unproved, {outcomes['proved']} accepted, {outcomes['timeout']} timeouts | 18 ReLU/GEMM mutants; 10 sum-proxy mutants |",
        f"| Equivalent positive controls | {positives}/6 accepted | Index-plus-zero rewrites |",
        f"| Large HIP programs | {gpu_good}/17 passed; {checks} numerical comparisons | All Table 9 workload dimensions; independently declared contracts |",
        f"| Exact certified HIP source | {exact}/90 exact GPU comparisons | Nine reduced sources, with source/reference/task/proof hashes |",
        f"| Scalar operations | {len(calibration['ops']) * calibration['pairs']} comparisons; {calibration['mismatches']} mismatches | Four operations, finite dyadic strata; Float64-to-FP32 comparison |",
        f"| Reported production address conflict | {race['status']} | Threads 0/80, output cell 50256; pinned upstream access formula |",
        f"| Reference AST versus CPU PyTorch | {validation['torch_comparisons']} comparisons passed | Examples, reduced fixtures, larger spatial/group/batch/broadcast cases |",
        "",
        "The original paper's 42-mutant set is unavailable. Our rejection counts do not "
        "reproduce its 42/42 result. A failed proof attempt does not establish a "
        "universal rejection guarantee. The sum proxy is not Softmax.",
        "",
        "## Reduced proof coverage",
        "",
        "| Family | Input shapes | Output shape | CUDA / HIP |",
        "| --- | --- | --- | --- |",
    ]
    for name in ("relu", "gemv", "gemm", "batchmatmul", "linear", "conv2d", "depthwise_conv"):
        task = json.loads((ROOT / "cases" / name / "task.json").read_text())
        inputs = ", ".join(str(b["shape"]) for b in task["buffers"] if b["role"] == "input")
        output = next(b["shape"] for b in task["buffers"] if b["role"] == "output")
        statuses = " / ".join(r["status"] for r in cpu["formal"] if r["task"] == name)
        lines.append(f"| {name} | {inputs} | {output} | {statuses} |")
    lines += [
        "",
        "SiLU, GELU, Softmax, LayerNorm and RMSNorm remain unsupported formally. "
        "There are no original-size FP16 or Level-2 certificates. "
        "CUDA profiles were checked on CPU and were not executed on NVIDIA hardware.",
        "",
        "## MI300X numerical checks and latency",
        "",
        f"Device: {gpu['device']} ({gpu['architecture']}); PyTorch {gpu['torch']}; "
        f"HIP runtime {gpu['torch_hip']}. Each numerical case uses six random trials "
        "and four probes, rtol=atol=0.01. Each latency is the median of seven rounds "
        "of a graph containing 20 calls, in microseconds; compilation is excluded.",
        "",
        "| Workload | Our HIP µs | Same-contract eager µs | Same-contract compiled µs | Max absolute error |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for r in gpu["cases"]:
        compiled = r.get("torch_compile", {}).get("median_us")
        compiled_text = f"{compiled:.3f}" if compiled is not None else "failed"
        error = max(c["max_abs_error"] for c in r["numerical_checks"])
        lines.append(
            f"| {r['task']} | {r['hip']['median_us']:.3f} | "
            f"{r['torch_eager']['median_us']:.3f} | {compiled_text} | {error:.6g} |"
        )
    slower = sum(
        r["hip"]["median_us"] > r["torch_compile"].get("median_us", float("inf"))
        for r in gpu["cases"]
    )
    lines += [
        "",
        f"Our simple HIP programs are slower than compiled PyTorch in {slower}/17 workloads. "
        "These measurements do not reproduce the paper's optimized kernels or claimed "
        "speedups. The references include FP16/FP32 conversion and are not a sweep of "
        "the fastest vendor implementations. All seven timing samples are retained in JSON.",
        "",
        "The five Level-2 AMD cases are extensions: the paper measures Level-2 on PTX/H100. "
        "Our dense attention workload implements the mathematical operation, not the "
        "FlashAttention algorithm. Contract choices and rounding/staging differences "
        "are documented in the methodology and JSON.",
        "",
        "## Small checker experiments",
        "",
        "| GEMM segment representation | Checked runs | Median Lean wall seconds |",
        "| --- | ---: | ---: |",
    ]
    for mode in ("grouped", "flat"):
        rows = [r for r in cpu["grouping_ablation"] if r["mode"] == mode]
        lines.append(
            f"| {mode} | {sum(r['accepted'] for r in rows)}/{len(rows)} | {statistics.median(r['wall_seconds'] for r in rows):.3f} |"
        )
    lines += [
        "",
        "| Product inner dimension | Lean result | Wall seconds |",
        "| ---: | --- | ---: |",
    ]
    for r in cpu["scaling"]:
        lines.append(f"| {r['inner_dimension']} | {r['outcome']} | {r['wall_seconds']:.3f} |")
    lines += [
        "",
        "These are small deterministic kernel-checker measurements, with other validation "
        "running concurrently. Grouping is a syntax change and does not reproduce the "
        "paper's induction/LLM ablation or its scalability claims.",
        "",
        "## Production race and trust boundary",
        "",
        "The checked witness uses C=50257, block size 1024, unroll factor 8. "
        "Thread 0's final-iteration slot 2 reads the clamped address min(50256,51200). "
        "Thread 80's slot 1 writes 50256. Both lie in the same block phase and different "
        "warps. Lean checks the actual `Lark.conflict` predicate for this pair and checks "
        "that the bounds guard excludes the reader. Both witness theorems use no axioms. "
        "[Proof source and log](results/production-race/).",
        "",
        "The upstream revision is pinned separately from the unavailable paper registry "
        "revision. Mapping source to this formula is trusted. This is not a full "
        "production-softmax correctness certificate. A tiny identity-valued reproducer "
        "has a race despite matching its reference for all symbolic inputs; the repaired "
        "version receives full reduced certificates and GPU numerical checks.",
        "",
        "Finite hardware comparisons do not establish IEEE semantics, error bounds or "
        "complete machine conformance. Reference/source translation and phase-reduction "
        "metatheory retain the trust boundary described in [the trust model](../docs/trust.md).",
        "",
        "Still unreproduced: original KernelCraft model pass rates/token costs; original "
        "FP16/PTX and production-kernel certificates; H100 timings; fastest-library "
        "speedups; model/induction ablations; complete opcode calibration and numerical "
        "error analysis. Missing original artifacts and unsupported semantics remain "
        "blockers independently of NVIDIA hardware access.",
        "",
    ]
    args.output.write_text("\n".join(lines))
    print(args.output)


if __name__ == "__main__":
    main()
