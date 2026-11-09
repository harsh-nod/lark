"""Complete pending independent mutation checks after a fully rechecked baseline run."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.certificate import render
from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import preflight
from lark_kernels.spec import read_spec
from reproduction.nonlinear.run_cpu import ROOT, MUTATIONS, direct, write


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", default="lean")
    p.add_argument("--timeout", type=float, default=180)
    p.add_argument("--jobs", type=int, default=4)
    args = p.parse_args()
    report = json.loads((args.output / "results.json").read_text())
    if len(report["formal"]) != 25 or not all(
        r["status"] == "verified" and r["rechecked"] for r in report["formal"]
    ):
        raise RuntimeError("A complete, previously rechecked baseline run is required")
    for row in report["formal"]:
        d = args.output / row["artifacts"]
        r = json.loads((d / "report.json").read_text())
        if any(sha(d / f) != value for f, value in r["files"].items()):
            raise RuntimeError("Baseline artifacts changed")
        task = Task.read(d / "task.json")
        tr = translate((d / "kernel.cu").read_text(), task)
        expected = render(
            task,
            tr,
            read_spec((d / "reference.py").read_text(), task),
            json.loads((d / "proposal.json").read_text()),
        )
        if expected != (d / "Main.lean").read_text():
            raise RuntimeError("Baseline theorem binding changed")
    report["completion_scheduler_sha256"] = sha(Path(__file__))
    report["completion_direct_module_sha256"] = sha(ROOT / "run_cpu.py")
    report["completion_jobs"] = args.jobs
    report["completion_note"] = (
        "Previously rechecked baseline proofs are reused after artifact and statement validation. Pending independent Lean checks run concurrently; wall times are not controlled performance measurements."
    )
    pending = []
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
            work = [("mutations", rule, source.replace(a, b, 1)) for rule, a, b in rules]
            before, after = ("a[t]", "a[t + 0]") if name == "gemm" else ("x[i]", "x[i + 0]")
            work.append(("positive_controls", "positive", source.replace(before, after, 1)))
            for category, rule, changed in work:
                existing = next(
                    (
                        r
                        for r in report[category]
                        if r["task"] == name
                        and r["language"] == language
                        and (category == "positive_controls" or r["rule"] == rule)
                    ),
                    None,
                )
                if existing:
                    d = args.output / existing["artifacts"]
                    for f, k in [
                        ("kernel.hip", "source_sha256"),
                        ("Main.lean", "theorem_sha256"),
                        ("lean.log", "log_sha256"),
                    ]:
                        if sha(d / f) != existing[k]:
                            raise RuntimeError("Completed check changed")
                    if (d / "kernel.hip").read_text() != changed:
                        raise RuntimeError("Completed mutant source changed")
                    continue
                dest = args.output / (
                    f"positive-{name}-{language}"
                    if rule == "positive"
                    else f"mutant-{name}-{language}-{rule}"
                )
                if dest.exists():
                    archived = dest.with_name("interrupted-" + dest.name)
                    if archived.exists():
                        raise RuntimeError("An interrupted artifact already exists")
                    dest.rename(archived)
                    report.setdefault("interrupted_checks", []).append(archived.name)
                pending.append((category, name, language, rule, task, changed, ref, dest))

    def run(item):
        category, name, language, rule, task, changed, ref, dest = item
        diagnostic = "passed"
        try:
            preflight(task, translate(changed, task), read_spec(ref, task))
        except Refusal as e:
            diagnostic = e.code
        row = direct(dest, task, changed, ref, args.lean, args.timeout)
        row.update(task=name, language=language)
        if category == "mutations":
            row.update(rule=rule, preflight_diagnostic=diagnostic, numeric_screen=False)
        return category, row

    print("Pending independent Lean checks:", len(pending), "jobs:", args.jobs, flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for future in as_completed([pool.submit(run, item) for item in pending]):
            category, row = future.result()
            report[category].append(row)
            write(args.output / "results.json", report)
            print(
                category,
                row["task"],
                row["language"],
                row.get("rule", "positive"),
                row["outcome"],
                flush=True,
            )
    write(args.output / "results.json", report)
    if len(report["mutations"]) != 28 or len(report["positive_controls"]) != 6:
        raise RuntimeError("Incomplete run")
    return int(
        any(r["accepted"] or r["outcome"] == "timeout" for r in report["mutations"])
        or any(not r["accepted"] for r in report["positive_controls"])
    )


if __name__ == "__main__":
    raise SystemExit(main())
