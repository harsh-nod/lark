"""Same-source GEMV flat-execution versus counted-loop induction experiment."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, gemv
from reproduction.reduction.make_cases import create


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    p.add_argument("--flat-timeout", type=float, default=30)
    args = p.parse_args()
    if args.flat_timeout <= 0:
        p.error("positive flat timeout required")
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "experiment": "same-source-gemv-flat-versus-induction",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "model_calls": 0,
        "runner_sha256": sha(Path(__file__)),
        "models": gemv.model_hashes(),
        "flat_timeout_seconds": args.flat_timeout,
        "pairs": [],
        "scope": "Independent same-source bounded FP16 GEMV. Timing includes Python/Lean elaboration. Flat means concrete symbolic execution/default proof slots; induction means pinned counted-loop/grid lemmas. Not the authors segmentation prompt ablation or original token/timing results.",
    }

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    for k in (1, 2, 4, 8, 16, 32, 64, 128):
        case = args.output / "cases" / str(k)
        create(case, n=2, k=k)
        pair = {
            "rows": 2,
            "reduction": k,
            "source_hashes": {
                n: sha(case / n) for n in ("kernel.hip", "reference.py", "task.json")
            },
            "methods": [],
        }
        for method, verify, timeout in (
            ("flat", certificate.verify, args.flat_timeout),
            ("induction", gemv.verify, 120),
        ):
            dest = args.output / method / str(k)
            start = time.monotonic()
            result = verify(
                case / "kernel.hip",
                case / "reference.py",
                case / "task.json",
                dest,
                lean=args.lean,
                timeout=timeout,
            )
            elapsed = time.monotonic() - start
            rechecked = False
            if result["status"] == "verified":
                certificate.check(dest, lean=args.lean, timeout=timeout)
                rechecked = True
            assert sha(dest / "kernel.cu") == pair["source_hashes"]["kernel.hip"]
            assert sha(dest / "reference.py") == pair["source_hashes"]["reference.py"]
            assert sha(dest / "task.json") == pair["source_hashes"]["task.json"]
            row = {
                "method": method,
                "status": result["status"],
                "rechecked": rechecked,
                "verify_seconds": elapsed,
                "timed_out": "Lean timed out" in (dest / "lean-1.log").read_text(),
                "main_bytes": (dest / "Main.lean").stat().st_size,
                "theorem_sha256": sha(dest / "Main.lean"),
            }
            pair["methods"].append(row)
            print(json.dumps({"k": k, **row}), flush=True)
        report["pairs"].append(pair)
        save()
    report["status"] = (
        "passed"
        if all(
            p["methods"][1]["status"] == "verified" and p["methods"][1]["rechecked"]
            for p in report["pairs"]
        )
        else "failed"
    )
    save()
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
