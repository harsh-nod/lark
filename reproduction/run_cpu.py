#!/usr/bin/env python3
"""Run reduced-shape formal, mutation, grouping, and scaling experiments offline."""

import argparse
from dataclasses import replace
from hashlib import sha256
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lark_kernels.certificate import (
    DEFAULT_PROOFS,
    check,
    default_segments,
    render,
    run_lean,
    verify,
)
from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import Machine, preflight
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent
FAMILIES = ("relu", "gemv", "gemm", "batchmatmul", "linear", "conv2d", "depthwise_conv")
MUTATIONS = {
    "relu": [
        ("R1", "0.0f", "1.0f"),
        ("R2", "x[i]", "x[(i + 1) % 4]"),
        ("R4", "fmaxf(v, 0.0f)", "fmaxf(0.0f, 0.0f)"),
        ("R5", "i < 4", "i < 3"),
    ],
    "gemm": [
        ("R1", "float acc = 0.0f", "float acc = 1.0f"),
        ("R2", "b[2 + t]", "b[t]"),
        ("R3", "__syncthreads();", ""),
        ("R4", "staged_b[k * 2 + t]", "staged_b[k * 2]"),
        ("R5", "k < 2", "k < 1"),
    ],
    "barrier_sum": [
        ("R1", "0.0f + staged[0]", "1.0f + staged[0]"),
        ("R2", "x[i]", "x[0]"),
        ("R3", "__syncthreads();", ""),
        ("R4", "staged[1]", "staged[0]"),
        ("R5", "j < 1", "j < 0"),
    ],
}


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


def write(p, d):
    p.write_text(json.dumps(d, indent=2) + "\n")


def direct(directory, task, source, reference, lean, timeout, segments=None):
    directory.mkdir(parents=True)
    tr = translate(source, task)
    spec = read_spec(reference, task)
    proposal = {
        "segments": default_segments(tr.program) if segments is None else segments,
        "proofs": dict(DEFAULT_PROOFS),
    }
    (directory / "kernel.hip").write_text(source)
    (directory / "reference.py").write_text(reference)
    (directory / "Main.lean").write_text(render(task, tr, spec, proposal))
    started = time.monotonic()
    ok, log = run_lean(directory, lean, timeout)
    (directory / "lean.log").write_text(log)
    return {
        "accepted": ok,
        "wall_seconds": time.monotonic() - started,
        "outcome": "proved" if ok else "timeout" if "Lean timed out" in log else "unproved",
        "source_sha256": digest(directory / "kernel.hip"),
        "theorem_sha256": digest(directory / "Main.lean"),
        "log_sha256": digest(directory / "lean.log"),
        "instructions": len(tr.program),
        "artifacts": str(directory.name),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", default="lean")
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--timeout", type=float, default=90)
    p.add_argument("--skip-mutations", action="store_true")
    p.add_argument("--skip-scaling", action="store_true")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "experiment": "independent-offline-reimplementation",
        "model_calls": 0,
        "paid_model_calls": 0,
        "numeric_screen_for_mutations": False,
        "model_sha256": digest(ROOT.parent / "lean/Lark/Model.lean"),
        "runner_sha256": digest(Path(__file__)),
        "formal": [],
        "mutations": [],
        "positive_controls": [],
        "grouping_ablation": [],
        "scaling": [],
        "limitations": [
            "Reduced float32 shapes, independent sources; not the paper's FP16 registry",
            "Five L1 families lack formal support: silu, gelu, softmax, layernorm, rmsnorm",
            "Mutation targets: ReLU/GEMM plus a sum/barrier proxy; no original Softmax/PTX mutant reproduction",
            "Grouping ablation compares syntax representations only; not the paper's induction/proof-agent ablation",
            "No paid models; paper model pass rates, costs, and failure-analysis ablations are not reproduced",
        ],
    }

    def save():
        write(args.output / "results.json", report)

    for name in (*FAMILIES, "barrier_sum", "llmc_fixed"):
        case = ROOT / "cases" / name
        for language in ("cuda", "hip"):
            task = json.loads((case / "task.json").read_text())
            task["language"] = language
            task["launch"]["warp"] = 32 if language == "cuda" else 64
            pin = args.output / (name + "-" + language + "-task.json")
            write(pin, task)
            dest = args.output / (name + "-" + language)
            start = time.monotonic()
            result = verify(
                case / "kernel.hip",
                case / "reference.py",
                pin,
                dest,
                lean=args.lean,
                timeout=args.timeout,
            )
            row = {
                "task": name,
                "language": language,
                "status": result["status"],
                "wall_seconds": time.monotonic() - start,
                "accesses": result["accesses"],
                "source_sha256": result["files"]["kernel.cu"],
                "theorem_sha256": result["files"]["Main.lean"],
                "artifacts": dest.name,
                "rechecked": False,
            }
            if result["status"] == "verified":
                check(dest, lean=args.lean, timeout=args.timeout)
                row["rechecked"] = True
            report["formal"].append(row)
            save()
            print("formal", name, language, row["status"], flush=True)
    # The unsafe program computes precisely the same symbolic outputs as identity.
    case = ROOT / "cases/llmc_race"
    task = Task.read(case / "task.json")
    tr = translate((case / "kernel.hip").read_text(), task)
    spec = read_spec((case / "reference.py").read_text(), task)
    m = Machine(task, tr).run()
    race = m.race()
    report["benign_race"] = {
        "same_symbolic_outputs": m.outputs() == spec,
        "located": race is not None,
        "threads": [a.thread for a in race],
        "location": race[0].location,
        "source_sha256": digest(case / "kernel.hip"),
        "classification": "minimal final-pass reproducer, not the complete upstream softmax",
    }
    save()
    if not args.skip_mutations:
        for name, rules in MUTATIONS.items():
            case = ROOT / "cases" / name
            source = (case / "kernel.hip").read_text()
            reference = (case / "reference.py").read_text()
            for language in ("cuda", "hip"):
                task = replace(
                    Task.read(case / "task.json"),
                    language=language,
                    warp=32 if language == "cuda" else 64,
                )
                for rule, before, after in rules:
                    if before not in source:
                        raise RuntimeError((name, rule, before))
                    changed = source.replace(before, after, 1)
                    # Preflight is recorded for diagnostics, then deliberately bypassed.
                    diagnostic = "passed"
                    try:
                        preflight(task, translate(changed, task), read_spec(reference, task))
                    except Refusal as e:
                        diagnostic = e.code
                    row = direct(
                        args.output / (name + "-" + language + "-" + rule),
                        task,
                        changed,
                        reference,
                        args.lean,
                        args.timeout,
                    )
                    row.update(
                        task=name,
                        language=language,
                        rule=rule,
                        preflight=diagnostic,
                        paper_target=name in {"relu", "gemm"},
                    )
                    report["mutations"].append(row)
                    save()
                    print("mutant", name, language, rule, row["outcome"], flush=True)
                before = "a[t]" if name == "gemm" else "x[i]"
                after = "a[t + 0]" if name == "gemm" else "x[i + 0]"
                row = direct(
                    args.output / (name + "-" + language + "-positive"),
                    task,
                    source.replace(before, after, 1),
                    reference,
                    args.lean,
                    args.timeout,
                )
                row.update(task=name, language=language, change="index plus zero")
                report["positive_controls"].append(row)
                save()
    case = ROOT / "cases/gemm"
    task = Task.read(case / "task.json")
    source = (case / "kernel.hip").read_text()
    reference = (case / "reference.py").read_text()
    tr = translate(source, task)
    for mode in ("grouped", "flat"):
        segments = None if mode == "grouped" else [{"op": i} for i in range(len(tr.program))]
        for trial in range(2):
            row = direct(
                args.output / f"grouping-{mode}-{trial}",
                task,
                source,
                reference,
                args.lean,
                args.timeout,
                segments,
            )
            row.update(mode=mode, trial=trial)
            report["grouping_ablation"].append(row)
            save()
    if not args.skip_scaling:
        for k in (1, 2, 4, 8):
            data = {
                "name": "scaling",
                "entry": "scale",
                "language": "hip",
                "buffers": [
                    {"name": "a", "role": "input", "shape": [1, k], "dtype": "float32"},
                    {"name": "b", "role": "input", "shape": [k, 2], "dtype": "float32"},
                    {"name": "out", "role": "output", "shape": [1, 2], "dtype": "float32"},
                ],
                "launch": {"grid": 1, "block": 2, "warp": 64},
                "fuel": [256, 16, 16, 16],
            }
            source = f"""extern "C" __global__ void scale(const float* a,const float* b,float* out) {{
int t=threadIdx.x; int k=0; float acc=0.0f;
while(k<{k}) {{acc=acc+a[k]*b[k*2+t];k++;}} out[t]=acc;
}}"""
            row = direct(
                args.output / f"scaling-{k}",
                Task.parse(json.dumps(data)),
                source,
                "def reference(a,b):\n return a @ b\n",
                args.lean,
                args.timeout,
            )
            row["inner_dimension"] = k
            report["scaling"].append(row)
            save()
    failed = any(r["status"] != "verified" or not r["rechecked"] for r in report["formal"])
    failed |= any(r["accepted"] or r["outcome"] == "timeout" for r in report["mutations"])
    failed |= any(
        not r["accepted"]
        for r in report["positive_controls"] + report["grouping_ablation"] + report["scaling"]
    )
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
