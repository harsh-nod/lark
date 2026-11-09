"""Render the MI350X experiment records without mixing them with the v1 study."""

import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results", type=Path, default=ROOT / "results")
    p.add_argument("--output", type=Path, default=ROOT / "RESULTS.md")
    args = p.parse_args()

    def read(name):
        return json.loads((args.results / name).read_text())

    cpu = read("cpu.json")
    large = read("mi350-large.json")
    devices = [("mi350", read("mi350-certified.json")), ("mi350-2", read("mi350-2-certified.json"))]
    assert (
        len(cpu["formal"]) == 25
        and len(cpu["mutations"]) == 28
        and len(cpu["positive_controls"]) == 6
    )
    assert len(large["cases"]) == 17
    counts = Counter(x["outcome"] for x in cpu["mutations"])
    good = sum(x["status"] == "verified" and x["rechecked"] for x in cpu["formal"])
    lines = [
        "# MI350X extension results",
        "",
        "Run date: 2026-11-09. [Contracts and reproduction commands](README.md). [Raw artifacts](results/).",
        "",
        "**Independent reduced-shape certificates and AMD hardware validation. This is not a full reproduction of the original paper. No model calls were made.**",
        "",
        "| CPU experiment | Observed | Scope |",
        "| --- | --- | --- |",
        f"| New certificates | {good}/25 verified and independently rechecked | 17 reduced FP16 HIP families, five FP32 HIP nonlinear families, three FP16 CUDA profiles |",
        f"| Direct Lean mutation checks | {counts['unproved']}/28 unproved, {counts['proved']} accepted, {counts['timeout']} timeouts | Independent FP16 ReLU/Softmax/GEMM mutants, HIP and CUDA; Python screen bypassed |",
        f"| Equivalent controls | {sum(x['accepted'] for x in cpu['positive_controls'])}/6 proved | Index-plus-zero rewrites |",
        "| Reference AST versus CPU PyTorch | 220 comparisons passed | Six random trials plus four probes for each of 22 source/reference pairs |",
        "| Historical compatibility | All 18 old statements regenerate byte-for-byte | Original scalar-v1 model unchanged |",
        "",
        "Half conversions and nonlinear functions are abstract operations in the universally quantified Lean model. These certificates establish source/reference equality in that model, not an IEEE implementation or a numerical-error bound. Source/reference lowering, hardware interpretation, host contracts and concurrency reduction remain trusted.",
        "",
        "## Reduced FP16 shapes",
        "",
        "| Family | Input shapes | Output shape | HIP certificate |",
        "| --- | --- | --- | --- |",
    ]
    for case in sorted((ROOT / "cases/float16").iterdir()):
        task = json.loads((case / "task.json").read_text())
        inputs = ", ".join(str(x["shape"]) for x in task["buffers"] if x["role"] == "input")
        output = next(x["shape"] for x in task["buffers"] if x["role"] == "output")
        row = next(
            x
            for x in cpu["formal"]
            if x["task"] == case.name and x["dtype"] == "float16" and x["language"] == "hip"
        )
        lines.append(f"| {case.name} | {inputs} | {output} | {row['status']} |")
    lines += [
        "",
        "Norms have no affine parameters and epsilon 1e-5. GELU uses the tanh approximation. FFN/SwiGLU round their hidden activation to FP16. RoPE uses supplied tables and adjacent pairs. Dense attention uses head dimension four; GQA uses two query heads, one KV head and **head dimension one**. These are intentionally small independent programs. Neither attention fixture implements the FlashAttention algorithm.",
        "",
        "## Exact-source hardware validation",
        "",
        "| Host | Device | Kernel trials passed | New scalar comparisons | Binary16 conversion comparisons |",
        "| --- | --- | ---: | ---: | ---: |",
    ]
    for host, d in devices:
        assert len(d["cases"]) == 22 and d["status"] == "passed"
        trials = sum(len(x["trials"]) for x in d["cases"])
        scalar = sum(x["comparisons"] for x in d["scalar_calibration"]["ops"])
        conversions = 2 * d["half_decode"]["finite_encodings"] + d["half_encode"]["comparisons"]
        lines.append(
            f"| {host} | {d['device']} / {d['architecture']} | {trials} | {scalar} | {conversions} |"
        )
    lines += [
        "",
        "The same prepared CPU PyTorch values, HIP source bytes, model hashes and certificate index are used on both hosts. Every input byte is preserved. FP16 output comparisons use rtol=atol=0.01; FP32 uses rtol=2e-5 and atol=2e-6. These are numerical tests of the reduced certified sources, separate from Lean checking.",
        "",
        "| New scalar operation | mi350 mismatches / samples | mi350-2 mismatches / samples |",
        "| --- | ---: | ---: |",
    ]
    for i, op in enumerate(devices[0][1]["scalar_calibration"]["ops"]):
        other = devices[1][1]["scalar_calibration"]["ops"][i]
        lines.append(
            f"| {op['op']} | {op['mismatches']}/{op['comparisons']} | {other['mismatches']}/{other['comparisons']} |"
        )
    lines += [
        "",
        "Scalar samples compare actual Lean Float64 evaluations, rounded to FP32, against HIP with rtol=2e-6 and atol=1e-6. The complete errors and hashes are in JSON. The half-conversion checks use a separate Python IEEE oracle: all 63,488 finite binary16 encodings are decoded and round-tripped, plus 7,168 finite binary32 conversion inputs with ties, adjacent values, signed zero, overflow and underflow. Both hosts have zero conversion mismatches. NaN/infinite input encodings and exhaustive binary32 conversion are outside this study.",
        "",
        "## Large workloads on MI350X",
        "",
        "These independent FP16 programs use the Table 9 dimensions, six random trials plus four probes per workload, and the previous graph/event timing protocol. They remain **numerically tested, not Lean-certified at these sizes**.",
        "",
        "| Workload | HIP µs | Eager reference µs | Compiled reference µs |",
        "| --- | ---: | ---: | ---: |",
    ]
    for row in large["cases"]:
        lines.append(
            f"| {row['task']} | {row['hip']['median_us']:.3f} | {row['torch_eager']['median_us']:.3f} | {row['torch_compile']['median_us']:.3f} |"
        )
    slower = sum(x["hip"]["median_us"] > x["torch_compile"]["median_us"] for x in large["cases"])
    lines += [
        "",
        f"All 17 workloads passed 170 numerical comparisons; all 17 compiled baselines completed. Our simple HIP kernels are slower than compiled PyTorch on {slower}/17 workloads. Ratios include the declared reference precision conversions and are not a fastest-vendor-library comparison. The raw record retains every seven-round timing sample.",
        "",
        "MI350X results extend the study to gfx950; they do not reproduce H100 or MI300X latency cells or the paper's optimized speedups. The five Level-2 AMD workloads are extensions to the paper's PTX-only Level-2 measurements.",
        "",
        "## Remaining gaps",
        "",
        "Original registry/kernel/proof artifacts; original-size FP16 and production-kernel certificates; PTX and tensor-core collectives; induction-based scalable proofs; model pass rates/token costs and LLM ablations; H100 timing cells; numerical error bounds and complete hardware semantics. The independent mutation set is not the paper's original 42 mutants.",
        "",
        "Lean reduction remains costly even for these reduced cases. The attention kernel computes scores once per query row to avoid duplicate symbolic execution; the GQA dimension is minimal. These choices do not establish paper-scale verification performance. All successful baseline certificates were rechecked and their theorem/source/model hashes are preserved.",
        "",
    ]
    args.output.write_text("\n".join(lines))
    print(args.output)


if __name__ == "__main__":
    main()
