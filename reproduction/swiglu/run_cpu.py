"""Full-size SwiGLU exports, wired-pipeline rechecks and symbolic scaling."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, swiglu
from lark_kernels.frontend import translate
from reproduction.swiglu.make_cases import create

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
        "experiment": swiglu.PROFILE,
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "models": swiglu.model_hashes(),
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
        result = swiglu.verify(case, dest, lean=args.lean)
        elapsed = time.monotonic() - started
        checked = False
        if result["status"] == "verified":
            certificate.check(dest, lean=args.lean)
            checked = True
        row = {
            "key": key,
            "status": result["status"],
            "rechecked": checked,
            "swiglu_dimensions": result["swiglu_dimensions"],
            "verify_seconds": elapsed,
            "main_bytes": (dest / "Main.lean").stat().st_size,
            "source_hashes": {f: sha(dest / f) for f in swiglu.SOURCE_FILES},
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
    values = {
        name: (case / (name.replace(".cu", ".hip") if name.endswith(".cu") else name)).read_text()
        for name in swiglu.SOURCE_FILES
    }
    tasks, trs = swiglu.prepare(values)
    for name, stage, old, new in (
        ("early-half", 0, "gate[i] = acc;", "gate[i] = __half2float(__float2half(acc));"),
        ("wrong-silu", 2, "expf(0.0f - a)", "expf(a)"),
        ("down-address", 3, "i % 256", "i % 128"),
    ):
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        key = swiglu.STAGES[stage] + ".cu"
        changed = values[key].replace(old, new)
        assert changed != values[key]
        (dest / "kernel.hip").write_text(changed)
        changed_trs = trs.copy()
        changed_trs[stage] = translate(changed, tasks[stage])
        (dest / "Main.lean").write_text(swiglu.render(tasks, changed_trs))
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
