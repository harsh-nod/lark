"""Check a small, independently adapted vLLM scalar activation and four controls."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels.certificate import (
    DEFAULT_PROOFS,
    check,
    default_segments,
    render,
    run_lean,
    verify,
)
from lark_kernels.frontend import translate
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def worker(output, lean, timeout):
    output.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/silu_and_mul"
    source = (case / "kernel.cu").read_text()
    reference = (case / "reference.py").read_text()
    signature = json.loads((case / "task.json").read_text())

    def positive(language):
        path = output / language
        path.mkdir()
        task = json.loads(json.dumps(signature))
        task["language"] = language
        task["launch"]["warp"] = 64 if language == "hip" else 32
        write(path / "task.json", task)
        start = time.monotonic()
        verify(
            case / "kernel.cu",
            case / "reference.py",
            path / "task.json",
            path / "certificate",
            lean=lean,
            timeout=timeout,
        )
        log = check(path / "certificate", lean=lean, timeout=timeout)
        (path / "fresh-check.log").write_text(log)
        return {
            "language": language,
            "status": "verified",
            "rechecked": True,
            "wall_seconds": time.monotonic() - start,
            "source_sha256": sha(case / "kernel.cu"),
            "reference_sha256": sha(case / "reference.py"),
            "theorem_sha256": sha(path / "certificate/Main.lean"),
            "report_sha256": sha(path / "certificate/report.json"),
        }

    mutants = [
        (
            "drop-intermediate-half-rounding",
            "__half2float(__float2half(x / (1.0f + expf((0.0f - x) * 1.0f))))",
            "x / (1.0f + expf((0.0f - x) * 1.0f))",
        ),
        ("wrong-token-stride", "token_idx * 2 * 5", "token_idx * 5"),
        ("wrong-gating-half", "idx + 5]", "idx + 4]"),
        ("omit-last-output", "idx < 5", "idx < 4"),
    ]

    def negative(item):
        name, old, new = item
        if old not in source:
            raise ValueError("Mutation anchor missing: " + name)
        changed = source.replace(old, new)
        path = output / name
        path.mkdir()
        task = Task.parse(json.dumps(signature))
        tr = translate(changed, task)
        spec = read_spec(reference, task)
        proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
        (path / "kernel.cu").write_text(changed)
        (path / "reference.py").write_text(reference)
        write(path / "task.json", signature)
        (path / "Main.lean").write_text(render(task, tr, spec, proposal))
        start = time.monotonic()
        accepted, log = run_lean(path, lean, timeout)
        (path / "lean.log").write_text(log)
        timed_out = "Lean timed out" in log
        if accepted or timed_out:
            raise RuntimeError("Negative control accepted/timed out: " + name)
        return {
            "name": name,
            "accepted": accepted,
            "timed_out": timed_out,
            "python_preflight_bypassed": True,
            "wall_seconds": time.monotonic() - start,
            "source_sha256": sha(path / "kernel.cu"),
            "theorem_sha256": sha(path / "Main.lean"),
            "log_sha256": sha(path / "lean.log"),
        }

    with ThreadPoolExecutor(max_workers=2) as pool:
        positives = list(pool.map(positive, ["hip", "cuda"]))
        negatives = list(pool.map(negative, mutants))
    report = {
        "status": "passed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "baselines": positives,
        "mutants": negatives,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": "Whole-launch certificates for an independently adapted scalar vLLM SiLU-and-mul at two tokens, hidden width five. Original paper registry/revision unavailable; no general upstream equivalence or IEEE proof. Four independent controls are direct Lean checks, not the original paper mutants.",
    }
    write(output / "results.json", report)
    write(
        output / "manifest.json",
        {str(p.relative_to(output)): sha(p) for p in sorted(output.rglob("*")) if p.is_file()},
    )
    print(json.dumps({"status": "passed", "certificates": 2, "direct_lean_rejections": 4}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--timeout", type=float, default=150)
    parser.add_argument("--frozen-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.frozen_worker:
        worker(args.output.resolve(), args.lean, args.timeout)
        return
    args.output.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix="lark-production-activation-source-") as d:
        frozen = Path(d)
        sources = list((ROOT / "lark_kernels").glob("*.py"))
        sources += list((ROOT / "lean").rglob("*.lean"))
        sources += [
            p
            for p in HERE.rglob("*")
            if p.is_file()
            and "__pycache__" not in p.parts
            and "results" not in p.relative_to(HERE).parts
        ]
        for source in sources:
            dest = frozen / source.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, dest)
        write(
            args.output / "source-manifest.json",
            {str(p.relative_to(frozen)): sha(p) for p in sorted(frozen.rglob("*")) if p.is_file()},
        )
        with tarfile.open(args.output / "source.tar.gz", "w:gz") as tar:
            for p in sorted(frozen.rglob("*")):
                if p.is_file():
                    tar.add(p, arcname=str(p.relative_to(frozen)))
        subprocess.run(
            [
                sys.executable,
                str(frozen / Path(__file__).relative_to(ROOT)),
                "--frozen-worker",
                "--output",
                str(args.output.resolve() / "cpu"),
                "--lean",
                args.lean,
                "--timeout",
                str(args.timeout),
            ],
            check=True,
            cwd=frozen,
        )


if __name__ == "__main__":
    main()
