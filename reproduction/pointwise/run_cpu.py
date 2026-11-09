"""Recheck full-length certificates, direct arithmetic mutants, and scaling evidence."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, pointwise
from reproduction.pointwise.make_cases import create

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    p.add_argument("--flat-timeout", type=float, default=30)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "experiment": "pointwise-induction-v3",
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "runner_sha256": sha(Path(__file__)),
        "models": pointwise.model_hashes(),
        "baselines": [],
        "mutants": [],
        "scaling": [],
        "scope": "Independent FP16 pointwise sources; full existing runLaunch semantics. Original paper launches, kernels and LLM ablations unavailable.",
    }

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(key, case, *, flat=False, recheck=True):
        task = json.loads((case / "task.json").read_text())
        source = case / ("kernel.hip" if task["language"] == "hip" else "kernel.cu")
        destination = args.output / key
        start = time.monotonic()
        record = (certificate.verify if flat else pointwise.verify)(
            source,
            case / "reference.py",
            case / "task.json",
            destination,
            lean=args.lean,
            timeout=args.flat_timeout if flat else 120,
        )
        elapsed = time.monotonic() - start
        checked = None
        check_elapsed = None
        if record["status"] == "verified" and recheck:
            started = time.monotonic()
            certificate.check(destination, lean=args.lean, timeout=120)
            check_elapsed = time.monotonic() - started
            checked = True
        row = {
            "key": key,
            "status": record["status"],
            "elements": task["buffers"][0]["shape"][0],
            "source_sha256": sha(source),
            "reference_sha256": sha(case / "reference.py"),
            "task_sha256": sha(case / "task.json"),
            "theorem_sha256": sha(destination / "Main.lean"),
            "verify_seconds": elapsed,
            "rechecked": checked,
            "recheck_seconds": check_elapsed,
            "main_bytes": (destination / "Main.lean").stat().st_size,
            "timed_out": "Lean timed out" in (destination / "lean-1.log").read_text(),
        }
        print(json.dumps(row), flush=True)
        return row

    jobs = [
        (f"baselines/{language}/{family}", ROOT / "cases" / language / family)
        for language in ("hip", "cuda")
        for family in ("relu", "silu", "gelu")
    ]
    # Compiler subprocess concurrency, not LLM workers or agents.
    with ThreadPoolExecutor(max_workers=3) as pool:
        report["baselines"] = list(pool.map(lambda job: run(*job), jobs))
    save()
    for language in ("hip", "cuda"):
        for family in ("relu", "silu", "gelu"):
            case = args.output / "mutant-cases" / language / family
            create(case, family, language)
            source = case / ("kernel.hip" if language == "hip" else "kernel.cu")
            old, new = {
                "relu": ("fmaxf(v, 0.0f)", "v + 0.0f"),
                "silu": ("1.0f + expf", "2.0f + expf"),
                "gelu": ("0.5f * v", "0.25f * v"),
            }[family]
            text = source.read_text()
            assert text.count(old) == 1
            source.write_text(text.replace(old, new))
            # prepare deliberately permits a DIFFERENT scalar reference body.
            # Lean must reject it; no Python numerical/equality screen is used.
            report["mutants"].append(run(f"mutants/{language}/{family}", case))
            save()
    for n in (1, 4, 16, 64, 256, 16384, 1048576, 2147483647):
        case = args.output / "scaling-cases" / str(n)
        create(case, "relu", "hip", n)
        row = run(f"scaling/induction/{n}", case, recheck=False)
        row["method"] = "induction"
        report["scaling"].append(row)
        save()
        if n <= 64:
            row = run(f"scaling/flat/{n}", case, flat=True, recheck=False)
            row["method"] = "flat"
            report["scaling"].append(row)
            save()
    expected = all(r["status"] == "verified" and r["rechecked"] for r in report["baselines"])
    expected &= all(r["status"] == "unproved" and not r["timed_out"] for r in report["mutants"])
    expected &= all(
        r["status"] == "verified" for r in report["scaling"] if r["method"] == "induction"
    )
    report["status"] = "passed" if expected else "failed"
    save()
    if not expected:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
