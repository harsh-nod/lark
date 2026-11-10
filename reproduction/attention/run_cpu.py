"""Full-size dense SDPA/GQA exports, three-stage rechecks and symbolic scaling."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, attention
from lark_kernels.frontend import translate
from reproduction.attention.make_cases import create

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
        "experiment": attention.PROFILE,
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "models": attention.model_hashes(),
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
        result = attention.verify(case, dest, lean=args.lean)
        elapsed = time.monotonic() - started
        checked = False
        if result["status"] == "verified":
            certificate.check(dest, lean=args.lean)
            checked = True
        row = {
            "key": key,
            "status": result["status"],
            "rechecked": checked,
            "attention_dimensions": result["attention_dimensions"],
            "verify_seconds": elapsed,
            "main_bytes": (dest / "Main.lean").stat().st_size,
            "source_hashes": {f: sha(dest / f) for f in attention.SOURCE_FILES},
            "theorem_sha256": sha(dest / "Main.lean"),
        }
        print(json.dumps(row), flush=True)
        return row

    for family in ("dense", "gqa"):
        for language in ("hip", "cuda"):
            report["baselines"].append(
                run(ROOT / "cases" / family / language, "baselines/" + family + "/" + language)
            )
            save()
    for kv_heads, groups, seq, dim in (
        (1, 1, 1, 1),
        (2, 2, 2, 4),
        (1, 1, 4096, 64),
        (2, 4, 128, 1048576),
    ):
        name = f"{kv_heads}-{groups}-{seq}-{dim}"
        case = args.output / "scaling-cases" / name
        create(case, kv_heads=kv_heads, groups=groups, seq=seq, dim=dim)
        report["scaling"].append(run(case, "scaling/" + name))
        save()
    case = ROOT / "cases/gqa/hip"
    values = {
        name: (case / (name.replace(".cu", ".hip") if name.endswith(".cu") else name)).read_text()
        for name in attention.SOURCE_FILES
    }
    tasks, trs = attention.prepare(values)
    for name, stage, old, new in (
        ("wrong-group", 0, "/ 4)", "/ 2)"),
        ("wrong-scale", 0, "acc / 8.0f", "acc / 4.0f"),
        ("wrong-softmax-start", 1, "j = 1;", "j = 0;"),
        ("wrong-value-head", 2, "/ 4)", "/ 2)"),
    ):
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        key = attention.STAGES[stage] + ".cu"
        changed = values[key].replace(old, new)
        assert changed != values[key]
        (dest / "kernel.hip").write_text(changed)
        changed_trs = trs.copy()
        changed_trs[stage] = translate(changed, tasks[stage])
        (dest / "Main.lean").write_text(attention.render(tasks, changed_trs))
        started = time.monotonic()
        ok, log = certificate.run_lean(dest, args.lean, 120)
        (dest / "lean.log").write_text(log)
        report["mutants"].append(
            {
                "name": name,
                "stage": stage,
                "accepted": ok,
                "timed_out": "Lean timed out" in log,
                "seconds": time.monotonic() - started,
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
