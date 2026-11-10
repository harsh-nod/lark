"""Full-shape HIP/CUDA normalizations exports, source-binding rechecks and reduction scaling."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, normalization
from lark_kernels.frontend import translate
from reproduction.normalization.make_cases import create

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "experiment": "normalization-induction-v9",
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "models": normalization.model_hashes(),
        "runner_sha256": sha(Path(__file__)),
        "baselines": [],
        "scaling": [],
        "mutants": [],
    }

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(case, key):
        source = case / ("kernel.hip" if (case / "kernel.hip").exists() else "kernel.cu")
        started = time.monotonic()
        dest = args.output / key
        result = normalization.verify(
            source, case / "reference.py", case / "task.json", dest, lean=args.lean, timeout=120
        )
        elapsed = time.monotonic() - started
        checked = False
        if result["status"] == "verified":
            certificate.check(dest, lean=args.lean)
            checked = True
        row = {
            "key": key,
            "status": result["status"],
            "rechecked": checked,
            "normalization_kind": result["normalization_kind"],
            "elements": result["elements"],
            "verify_seconds": elapsed,
            "main_bytes": (dest / "Main.lean").stat().st_size,
            "source_sha256": sha(source),
            "reference_sha256": sha(case / "reference.py"),
            "task_sha256": sha(case / "task.json"),
            "theorem_sha256": sha(dest / "Main.lean"),
        }
        print(json.dumps(row), flush=True)
        return row

    for kind in normalization.KINDS:
        for language in ("hip", "cuda"):
            report["baselines"].append(
                run(ROOT / "cases" / kind / language, f"baselines/{kind}/{language}")
            )
            save()
    for kind in normalization.KINDS:
        for n in (1, 1048576, 2147483647):
            case = args.output / "scaling-cases" / f"{kind}-{n}"
            create(case, kind, "hip", n)
            report["scaling"].append(run(case, f"scaling/{kind}-{n}"))
            save()
    # These direct Lean checks bypass the Python structural guard; each must
    # fail the obligation binding the actual IR to the fixed proved program.
    for kind, name, old, new in [
        ("rms", "square-arithmetic", "acc + val * val", "acc + val + val"),
        ("layer", "variance-centering", "(val - ctx) * (val - ctx)", "(val + ctx) * (val + ctx)"),
        ("softmax", "max-start", "int j = 1;", "int j = 0;"),
    ]:
        case = ROOT / "cases" / kind / "hip"
        source = (case / "kernel.hip").read_text()
        task, _, checked_kind = normalization.prepare(
            source, (case / "reference.py").read_text(), (case / "task.json").read_text()
        )
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        assert old in source
        changed = source.replace(old, new)
        (dest / "kernel.hip").write_text(changed)
        tr = translate(changed, task)
        (dest / "Main.lean").write_text(normalization.render(task, tr, checked_kind))
        started = time.monotonic()
        ok, log = certificate.run_lean(dest, args.lean, 120)
        (dest / "lean.log").write_text(log)
        report["mutants"].append(
            {
                "name": name,
                "accepted": ok,
                "timed_out": "Lean timed out" in log,
                "seconds": time.monotonic() - started,
                "source_sha256": sha(dest / "kernel.hip"),
                "theorem_sha256": sha(dest / "Main.lean"),
                "expected_failure": "fixed-program equality; not semantic mutation diagnosis",
            }
        )
        save()
    expected = all(
        r["status"] == "verified" and r["rechecked"]
        for r in report["baselines"] + report["scaling"]
    )
    expected &= all(not r["accepted"] and not r["timed_out"] for r in report["mutants"])
    report["status"] = "passed" if expected else "failed"
    save()
    if not expected:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
