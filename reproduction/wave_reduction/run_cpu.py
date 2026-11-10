"""Freeze and check one real wave-sum certificate, fresh recheck and direct controls."""

import argparse
from dataclasses import replace
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import collective, wave_sum  # noqa: E402
from lark_kernels.certificate import check, lean_binary  # noqa: E402
from lark_kernels.ir import node  # noqa: E402
from lark_kernels.real_backend import seed_project  # noqa: E402

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def worker(out, lean, timeout):
    out.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/sum64"
    cert = out / "certificate"
    start = time.monotonic()
    report = wave_sum.verify(
        case / "kernel.hip",
        case / "reference.py",
        case / "task.json",
        cert,
        lean=lean,
        timeout=timeout,
    )
    if report["status"] != "verified":
        raise RuntimeError("Positive certificate failed")
    (out / "fresh-check.log").write_text(check(cert, lean=lean, timeout=timeout))
    baseline = {
        "status": "verified",
        "rechecked": True,
        "wall_seconds": time.monotonic() - start,
        "theorem_sha256": sha(cert / "Main.lean"),
        "report_sha256": sha(cert / "report.json"),
    }
    print(json.dumps({"baseline": "verified", "fresh_check": "passed"}), flush=True)
    source, reference, task_source = [
        (case / n).read_text() for n in ("kernel.hip", "reference.py", "task.json")
    ]
    task, tr, refs = wave_sum.prepare(source, reference, task_source)
    controls = []
    for name, gate in (
        ("wrong-last-shuffle", "fixed-program equality"),
        ("last-reference-cell", "reference-cell equality"),
        ("all-reference-cells-plus-one", "canonical-reference equality"),
        ("wrong-launch", "actual-launch interface"),
    ):
        dest = out / name
        dest.mkdir()
        changed, ct, ctr, cr = source, task, tr, list(refs)
        if name == "wrong-last-shuffle":
            changed = source.replace("__shfl_xor(x, 1, 64)", "__shfl_xor(x, 2, 64)")
            ctr = collective.translate(changed, task)
        elif name == "last-reference-cell":
            cr[63] = node("input", 0, 0)
        elif name == "all-reference-cells-plus-one":
            cr = [node("bin", "add", r, node("lit", 1, 1)) for r in cr]
        else:
            ct = replace(task, block=128)
        main = wave_sum.render(ct, ctr, cr).encode()
        (dest / "Main.lean").write_bytes(main)
        (dest / "kernel.hip").write_text(changed)
        (dest / "reference.py").write_text(reference)
        raw = json.loads(task_source)
        raw["launch"]["block"] = ct.block
        write(dest / "task.json", raw)
        write(dest / "reference-nodes.json", [r.data() for r in cr])
        start = time.monotonic()
        accepted, log = wave_sum.validate_main(main, lean_binary(lean), timeout)
        (dest / "lean.log").write_text(log)
        timed_out = "Lean timed out" in log
        if (
            accepted
            or timed_out
            or "error:" not in log
            or "maximum number of heartbeats" in log
            or "maximum recursion" in log
        ):
            raise RuntimeError("Unexpected direct control outcome: " + name)
        controls.append(
            {
                "name": name,
                "accepted": accepted,
                "timed_out": timed_out,
                "failed_gate": gate,
                "python_profile_preflight_bypassed": True,
                "wall_seconds": time.monotonic() - start,
                "source_sha256": sha(dest / "kernel.hip"),
                "theorem_sha256": sha(dest / "Main.lean"),
                "log_sha256": sha(dest / "lean.log"),
            }
        )
        print(json.dumps({"control": name, "status": "rejected", "timeout": False}), flush=True)
    write(
        out / "results.json",
        {
            "status": "passed",
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "profile": wave_sum.PROFILE,
            "baseline": baseline,
            "controls": controls,
            "certificates": 1,
            "recorded_independent_rechecks": 1,
            "direct_lean_rejections": 4,
            "model_calls": 0,
            "original_paper_fully_reproduced": False,
            "scope": report["scope"],
            "negative_reference_note": "Formal reference-nodes sidecars are mutated; canonical Python reference source is retained for the direct reference controls. These are equality/interface gates, not original paper diagnosis channels.",
        },
    )
    write(
        out / "manifest.json",
        {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--frozen-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.frozen_worker:
        worker(args.output.resolve(), args.lean, args.timeout)
        return
    args.output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["LARK_REAL_PROJECT"] = str(seed_project())
    with tempfile.TemporaryDirectory(prefix="lark-wave-source-") as temporary:
        frozen = Path(temporary)
        sources = list((ROOT / "lark_kernels").glob("*.py"))
        sources += [p for p in (ROOT / "lean").rglob("*.lean") if ".lake" not in p.parts]
        sources += [
            ROOT / n
            for n in (
                "lean/lakefile.toml",
                "lean/lean-toolchain",
                "pyproject.toml",
                "LICENSE",
                "tests/test_wave_sum.py",
            )
        ]
        sources += [
            ROOT / "lean-real" / n
            for n in (
                "LarkReal.lean",
                "LarkReal/Ops.lean",
                "LarkReal/WaveSum.lean",
                "lakefile.toml",
                "lake-manifest.json",
                "lean-toolchain",
            )
        ]
        sources += [
            p
            for p in HERE.rglob("*")
            if p.is_file()
            and not {"results", "checkpoint", "__pycache__"} & set(p.relative_to(HERE).parts)
        ]
        for path in sorted(set(sources)):
            target = frozen / path.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        write(
            args.output / "source-manifest.json",
            {
                p.relative_to(frozen).as_posix(): sha(p)
                for p in sorted(frozen.rglob("*"))
                if p.is_file()
            },
        )
        with tarfile.open(args.output / "source.tar.gz", "w:gz") as archive:
            for p in sorted(frozen.rglob("*")):
                if p.is_file():
                    archive.add(p, arcname=p.relative_to(frozen), recursive=False)
        subprocess.run(
            [
                sys.executable,
                str(frozen / "reproduction/wave_reduction/run_cpu.py"),
                "--frozen-worker",
                "--output",
                str(args.output.resolve() / "cpu"),
                "--lean",
                args.lean,
                "--timeout",
                str(args.timeout),
            ],
            cwd=frozen,
            env=env,
            check=True,
        )


if __name__ == "__main__":
    main()
