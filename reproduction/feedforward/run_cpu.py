"""Full-size FFN exports, wired-pipeline rechecks and symbolic scaling."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, feedforward
from lark_kernels.frontend import translate
from reproduction.feedforward.make_cases import create

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
        "experiment": feedforward.PROFILE,
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "models": feedforward.model_hashes(),
        "runner_sha256": sha(Path(__file__)),
        "baselines": [],
        "scaling": [],
        "mutants": [],
    }

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(case, key):
        started = time.monotonic()
        dest = args.output / key
        result = feedforward.verify(case, dest, lean=args.lean)
        elapsed = time.monotonic() - started
        checked = False
        if result["status"] == "verified":
            certificate.check(dest, lean=args.lean)
            checked = True
        row = {
            "key": key,
            "status": result["status"],
            "rechecked": checked,
            "ffn_dimensions": result["ffn_dimensions"],
            "verify_seconds": elapsed,
            "main_bytes": (dest / "Main.lean").stat().st_size,
            "source_hashes": {
                f: sha(dest / f)
                for f in ("up.cu", "down.cu", "reference.py", "up-task.json", "down-task.json")
            },
            "theorem_sha256": sha(dest / "Main.lean"),
        }
        print(json.dumps(row), flush=True)
        return row

    for language in ("hip", "cuda"):
        report["baselines"].append(run(ROOT / "cases" / language, "baselines/" + language))
        save()
    for m, k, h, n in ((1, 1, 1, 1), (64, 1048576, 16, 256), (1024, 256, 1024, 1024)):
        name = f"{m}-{k}-{h}-{n}"
        case = args.output / "scaling-cases" / name
        create(case, m=m, k=k, h=h, n=n)
        report["scaling"].append(run(case, "scaling/" + name))
        save()
    case = ROOT / "cases/hip"
    values = [
        (case / f).read_text()
        for f in ("up.hip", "down.hip", "reference.py", "up-task.json", "down-task.json")
    ]
    tasks, trs = feedforward.prepare(*values)
    for name, stage, old, new in (
        ("missing-relu", 0, "fmaxf(acc, 0.0f)", "acc"),
        ("up-arithmetic", 0, "acc = acc +", "acc = acc -"),
        ("down-address", 1, "i % 256", "i % 128"),
    ):
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        changed = values[stage].replace(old, new)
        assert changed != values[stage]
        (dest / "kernel.hip").write_text(changed)
        changed_trs = trs.copy()
        changed_trs[stage] = translate(changed, tasks[stage])
        (dest / "Main.lean").write_text(feedforward.render(tasks, changed_trs))
        start = time.monotonic()
        ok, log = certificate.run_lean(dest, args.lean, 120)
        (dest / "lean.log").write_text(log)
        report["mutants"].append(
            {
                "name": name,
                "stage": stage,
                "accepted": ok,
                "timed_out": "Lean timed out" in log,
                "seconds": time.monotonic() - start,
                "source_sha256": sha(dest / "kernel.hip"),
                "theorem_sha256": sha(dest / "Main.lean"),
                "expected_failure": "fixed-program equality; not semantic diagnosis",
            }
        )
        save()
    passed = all(
        r["status"] == "verified" and r["rechecked"]
        for r in report["baselines"] + report["scaling"]
    )
    passed &= all(not r["accepted"] and not r["timed_out"] for r in report["mutants"])
    report["status"] = "passed" if passed else "failed"
    save()
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
