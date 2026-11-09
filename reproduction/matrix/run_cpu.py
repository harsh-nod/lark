"""Full-shape HIP/CUDA GEMM and batched GEMM exports, source-binding rechecks and reduction scaling."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, matrix
from lark_kernels.frontend import translate
from reproduction.matrix.make_cases import create

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
        "experiment": "matrix-induction-v5",
        "model_calls": 0,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "models": matrix.model_hashes(),
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
        result = matrix.verify(
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
            "matrix_dimensions": result["matrix_dimensions"],
            "verify_seconds": elapsed,
            "main_bytes": (dest / "Main.lean").stat().st_size,
            "source_sha256": sha(source),
            "reference_sha256": sha(case / "reference.py"),
            "task_sha256": sha(case / "task.json"),
            "theorem_sha256": sha(dest / "Main.lean"),
        }
        print(json.dumps(row), flush=True)
        return row

    for language in ("hip", "cuda"):
        for family in ("gemm", "bmm"):
            report["baselines"].append(
                run(ROOT / "cases" / language / family, "baselines/" + language + "/" + family)
            )
            save()
    for family, batch, m, k, n in [
        ("gemm", 1, 1, 1, 1),
        ("gemm", 1, 64, 256, 512),
        ("gemm", 1, 64, 1048576, 512),
        ("bmm", 32, 64, 256, 512),
        ("bmm", 256, 4096, 16, 1024),
    ]:
        label = f"{family}-{batch}-{m}-{k}-{n}"
        case = args.output / "scaling-cases" / label
        create(case, "hip", family, batch, m, k, n)
        report["scaling"].append(run(case, "scaling/" + label))
        save()
    # Bypass the profile's structural screen. Emit the changed actual IR against
    # the original fixed program/reference obligations and send it to Lean.
    case = ROOT / "cases/hip/bmm"
    source = (case / "kernel.hip").read_text()
    task, _ = matrix.prepare(
        source, (case / "reference.py").read_text(), (case / "task.json").read_text()
    )
    for name, old, new in [
        ("arithmetic", "acc = acc +", "acc = acc -"),
        ("batch-address", "i / 32768", "i / 16384"),
        ("loop", "j < 256", "j < 255"),
    ]:
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        changed = source.replace(old, new)
        (dest / "kernel.hip").write_text(changed)
        tr = translate(changed, task)
        (dest / "Main.lean").write_text(matrix.render(task, tr))
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
