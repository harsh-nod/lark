"""Certify the nonlinear/half fixtures and directly check independent mutants."""

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.certificate import (
    verify,
    check,
    render,
    default_segments,
    DEFAULT_PROOFS,
    run_lean,
)
from lark_kernels.frontend import translate
from lark_kernels.ir import Task, Refusal
from lark_kernels.machine import preflight
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent
MUTATIONS = {
    "relu": [
        ("R1", "0.0f", "1.0f"),
        ("R2", "x[i]", "x[(i + 1) % 4]"),
        ("R4", "fmaxf(v, 0.0f)", "fmaxf(0.0f, 0.0f)"),
        ("R5", "i < 4", "i < 3"),
    ],
    "softmax": [
        ("R1", "float total = 0.0f", "float total = 1.0f"),
        ("R2", "x[i]", "x[(i + 1) % 4]"),
        ("R3", "__syncthreads();", ""),
        ("R4", "weights[i] / total", "weights[0] / total"),
        ("R5", "k < 4", "k < 3"),
    ],
    "gemm": [
        ("R1", "float acc = 0.0f", "float acc = 1.0f"),
        ("R2", "__half2float(b[2 + t])", "__half2float(b[t])"),
        ("R3", "__syncthreads();", ""),
        ("R4", "staged_b[k * 2 + t]", "staged_b[k * 2]"),
        ("R5", "k < 2", "k < 1"),
    ],
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(p, data):
    p.write_text(json.dumps(data, indent=2) + "\n")


def direct(dest, task, source, reference, lean, timeout):
    dest.mkdir()
    tr = translate(source, task)
    spec = read_spec(reference, task)
    (dest / "kernel.hip").write_text(source)
    (dest / "reference.py").write_text(reference)
    proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
    (dest / "Main.lean").write_text(render(task, tr, spec, proposal))
    start = time.monotonic()
    ok, log = run_lean(dest, lean, timeout)
    (dest / "lean.log").write_text(log)
    return {
        "accepted": ok,
        "outcome": "proved" if ok else "timeout" if "Lean timed out" in log else "unproved",
        "wall_seconds": time.monotonic() - start,
        "source_sha256": sha(dest / "kernel.hip"),
        "theorem_sha256": sha(dest / "Main.lean"),
        "log_sha256": sha(dest / "lean.log"),
        "artifacts": dest.name,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", default="lean")
    p.add_argument("--timeout", type=float, default=180)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "experiment": "nonlinear-v2-independent-reduced-shapes",
        "model_calls": 0,
        "model_sha256": sha(ROOT.parents[1] / "lean/Lark/Nonlinear.lean"),
        "runner_sha256": sha(Path(__file__)),
        "formal": [],
        "mutations": [],
        "positive_controls": [],
        "scope": "Reduced shapes only. Half storage and scalar functions are abstract operations, universally quantified. No IEEE numerical-error guarantee, original-size proof, or tensor-core/inductive proof.",
    }
    index = {}

    def save():
        write(args.output / "results.json", report)
        write(args.output / "certificate-index.json", index)

    cases = sorted((ROOT / "cases").glob("*/*"))
    for case in cases:
        languages = (
            ("hip", "cuda")
            if case.parent.name == "float16" and case.name in MUTATIONS
            else ("hip",)
        )
        for language in languages:
            data = json.loads((case / "task.json").read_text())
            data["language"] = language
            data["launch"]["warp"] = 64 if language == "hip" else 32
            stem = case.parent.name + "-" + case.name + "-" + language
            pin = args.output / (stem + "-task.json")
            write(pin, data)
            dest = args.output / stem
            start = time.monotonic()
            r = verify(
                case / "kernel.hip",
                case / "reference.py",
                pin,
                dest,
                lean=args.lean,
                timeout=args.timeout,
            )
            row = {
                "task": case.name,
                "dtype": case.parent.name,
                "language": language,
                "status": r["status"],
                "wall_seconds": time.monotonic() - start,
                "rechecked": False,
                "accesses": r["accesses"],
                "artifacts": dest.name,
            }
            if r["status"] == "verified":
                check(dest, lean=args.lean, timeout=args.timeout)
                row["rechecked"] = True
            report["formal"].append(row)
            if language == "hip":
                index[case.parent.name + "/" + case.name] = {
                    "status": r["status"],
                    "source_sha256": r["files"]["kernel.cu"],
                    "reference_sha256": r["files"]["reference.py"],
                    "task_sha256": r["files"]["task.json"],
                    "theorem_sha256": r["files"]["Main.lean"],
                    "model_sha256": r["model_sha256"],
                    "artifacts": dest.name,
                }
            save()
            print("formal", stem, r["status"], flush=True)
    for name, rules in MUTATIONS.items():
        case = ROOT / "cases/float16" / name
        source = (case / "kernel.hip").read_text()
        ref = (case / "reference.py").read_text()
        for language in ("hip", "cuda"):
            task = replace(
                Task.read(case / "task.json"),
                language=language,
                warp=64 if language == "hip" else 32,
            )
            for rule, a, b in rules:
                assert a in source, (name, rule)
                changed = source.replace(a, b, 1)
                diagnostic = "passed"
                try:
                    preflight(task, translate(changed, task), read_spec(ref, task))
                except Refusal as e:
                    diagnostic = e.code
                row = direct(
                    args.output / f"mutant-{name}-{language}-{rule}",
                    task,
                    changed,
                    ref,
                    args.lean,
                    args.timeout,
                )
                row.update(
                    task=name,
                    language=language,
                    rule=rule,
                    preflight_diagnostic=diagnostic,
                    numeric_screen=False,
                )
                report["mutations"].append(row)
                save()
                print("mutant", name, language, rule, row["outcome"], flush=True)
            before, after = ("a[t]", "a[t + 0]") if name == "gemm" else ("x[i]", "x[i + 0]")
            row = direct(
                args.output / f"positive-{name}-{language}",
                task,
                source.replace(before, after, 1),
                ref,
                args.lean,
                args.timeout,
            )
            row.update(task=name, language=language)
            report["positive_controls"].append(row)
            save()
    failed = any(r["status"] != "verified" or not r["rechecked"] for r in report["formal"])
    failed |= any(r["accepted"] or r["outcome"] == "timeout" for r in report["mutations"])
    failed |= any(not r["accepted"] for r in report["positive_controls"])
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
