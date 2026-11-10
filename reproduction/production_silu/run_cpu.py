"""Freeze and check scalable multiwave SiLU certificates and direct Lean controls."""

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
from lark_kernels import silu  # noqa: E402
from lark_kernels.certificate import check, run_lean  # noqa: E402
from lark_kernels.frontend import translate  # noqa: E402
from lark_kernels.ir import Node  # noqa: E402

HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(p, data):
    p.write_text(json.dumps(data, indent=2) + "\n")


def symbolic_case(path, name, rows, width):
    base = ROOT / "reproduction/production_activation/cases/silu_and_mul"
    path.mkdir()
    source = (base / "kernel.cu").read_text().replace("5", str(width))
    reference = (
        (base / "reference.py")
        .read_text()
        .replace("reshape(2, 2, 5)", f"reshape({rows}, 2, {width})")
    )
    task = json.loads((base / "task.json").read_text())
    task["name"] = name
    task["buffers"][0]["shape"] = [rows, width]
    task["buffers"][1]["shape"] = [rows, 2 * width]
    task["launch"] = {"grid": rows, "block": min(width, 1024), "warp": 64}
    task["fuel"] = [7 * width + 4, 1, 1, 1]
    (path / "kernel.cu").write_text(source)
    (path / "reference.py").write_text(reference)
    write(path / "task.json", task)


def worker(out, lean, timeout):
    out.mkdir(parents=True, exist_ok=False)
    work = []
    for case in sorted((HERE / "cases").iterdir()):
        for language in ("hip", "cuda"):
            work.append((case.name, case, language, False))
    for name, rows, width in (("symbolic-width", 1, 1073741823), ("symbolic-grid", 1073741823, 1)):
        case = out / (name + "-source")
        symbolic_case(case, name, rows, width)
        work.append((name, case, "hip", True))

    def positive(item):
        key, case, language, symbolic = item
        dest = out / (key + "-" + language)
        dest.mkdir()
        task = json.loads((case / "task.json").read_text())
        task["language"] = language
        task["launch"]["warp"] = 64 if language == "hip" else 32
        write(dest / "task.json", task)
        start = time.monotonic()
        report = silu.verify(
            case / "kernel.cu",
            case / "reference.py",
            dest / "task.json",
            dest / "certificate",
            lean=lean,
            timeout=timeout,
        )
        if report["status"] != "verified":
            raise RuntimeError("Positive certificate failed: " + str(item))
        log = check(dest / "certificate", lean=lean, timeout=timeout)
        (dest / "fresh-check.log").write_text(log)
        result = {
            "key": key,
            "language": language,
            "status": "verified",
            "rechecked": True,
            "symbolic_only": symbolic,
            "rows": report["rows"],
            "hidden": report["hidden"],
            "output_elements": report["output_elements"],
            "input_elements": report["input_elements"],
            "block": report["block"],
            "warp": report["warp"],
            "wall_seconds": time.monotonic() - start,
            "theorem_bytes": (dest / "certificate/Main.lean").stat().st_size,
            "theorem_sha256": sha(dest / "certificate/Main.lean"),
            "report_sha256": sha(dest / "certificate/report.json"),
        }
        print(
            json.dumps(
                {"baseline": key, "language": language, "status": "verified", "rechecked": True}
            ),
            flush=True,
        )
        return result

    source_case = HERE / "cases/full"
    source = (source_case / "kernel.cu").read_text()
    reference = (source_case / "reference.py").read_text()
    task_source = (source_case / "task.json").read_text()
    task, _, ref = silu.prepare(source, reference, task_source)
    controls = [
        ("wrong-input-half", "idx + 4097]", "idx + 4096]"),
        ("overlapping-loop-step", "idx + blockDim.x", "idx + 1"),
        ("omitted-last-column", "idx < 4097", "idx < 4096"),
        (
            "removed-source-half-rounding",
            "__half2float(__float2half(x / (1.0f + expf((0.0f - x) * 1.0f))))",
            "x / (1.0f + expf((0.0f - x) * 1.0f))",
        ),
        ("removed-reference-half-rounding", None, None),
    ]

    def negative(item):
        name, old, new = item
        dest = out / name
        dest.mkdir()
        changed, changed_ref = source, ref
        if old is not None:
            if old not in source:
                raise ValueError("Control anchor missing: " + name)
            changed = source.replace(old, new)
        else:

            def drop(n):
                if n.op == "un" and n.args[0] == "fromHalf":
                    inner = n.args[1]
                    if inner.op == "un" and inner.args[0] == "toHalf":
                        return inner.args[1]
                return Node(n.op, tuple(drop(a) if isinstance(a, Node) else a for a in n.args))

            changed_ref = drop(ref)
            if changed_ref == ref:
                raise ValueError("Reference control did not change")
        tr = translate(changed, task)
        (dest / "kernel.cu").write_text(changed)
        (dest / "reference.py").write_text(reference)
        (dest / "task.json").write_text(task_source)
        write(dest / "reference-node.json", changed_ref.data())
        (dest / "Main.lean").write_text(silu.render(task, tr, changed_ref))
        start = time.monotonic()
        accepted, log = run_lean(dest, lean, timeout)
        (dest / "lean.log").write_text(log)
        timed_out = "Lean timed out" in log
        if accepted or timed_out or "error:" not in log:
            raise RuntimeError("Unexpected control outcome: " + name)
        result = {
            "name": name,
            "accepted": accepted,
            "timed_out": timed_out,
            "python_profile_preflight_bypassed": True,
            "failed_gate": "reference-expression equality"
            if old is None
            else "fixed-program equality",
            "wall_seconds": time.monotonic() - start,
            "source_sha256": sha(dest / "kernel.cu"),
            "theorem_sha256": sha(dest / "Main.lean"),
            "log_sha256": sha(dest / "lean.log"),
        }
        print(json.dumps({"control": name, "status": "rejected", "timeout": False}), flush=True)
        return result

    with ThreadPoolExecutor(max_workers=2) as pool:
        baselines = list(pool.map(positive, work))
        mutants = list(pool.map(negative, controls))
    result = {
        "schema": 1,
        "status": "passed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "profile": silu.PROFILE,
        "baselines": baselines,
        "mutants": mutants,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": "Independent upstream-derived scalar FP16 SiLU-and-mul, retaining native multiwave blocks and the strided loop. Six HIP/CUDA certificates at selected device-test shapes and two symbolic-only billion-cell extremes; all are abstract-operation proofs. Original authors' production sources/runs, packed vector paths, IEEE theorems and NVIDIA execution remain absent. Five direct controls fail fixed-program/reference equality, not an original-paper diagnosis channel.",
    }
    write(out / "results.json", result)
    write(
        out / "manifest.json",
        {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
    )
    print(
        json.dumps(
            {
                "status": "passed",
                "certificates": len(baselines),
                "direct_lean_rejections": len(mutants),
            }
        ),
        flush=True,
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean", default="lean")
    p.add_argument("--timeout", default=150, type=float)
    p.add_argument("--frozen-worker", action="store_true", help=argparse.SUPPRESS)
    args = p.parse_args()
    if args.frozen_worker:
        worker(args.output.resolve(), args.lean, args.timeout)
        return
    args.output.mkdir(parents=True, exist_ok=False)
    legacy = ROOT / "reproduction/production_activation"
    with tempfile.TemporaryDirectory(prefix="lark-silu-source-") as d:
        frozen = Path(d)
        sources = list((ROOT / "lark_kernels").glob("*.py")) + list((ROOT / "lean").rglob("*.lean"))
        sources += list((ROOT / "tests").glob("*.py"))
        sources += [
            ROOT / p
            for p in ("pyproject.toml", "LICENSE", "lean/lakefile.toml", "lean/lean-toolchain")
        ]
        sources += [
            p
            for p in HERE.rglob("*")
            if p.is_file()
            and "__pycache__" not in p.parts
            and "results" not in p.relative_to(HERE).parts
        ]
        sources += [p for p in (legacy / "upstream").rglob("*") if p.is_file()]
        sources += [legacy / "prepare_gpu.py", legacy / "provenance.json"]
        sources += [p for p in (legacy / "cases/silu_and_mul").iterdir() if p.is_file()]
        for source in sources:
            target = frozen / source.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
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
            cwd=frozen,
            check=True,
        )


if __name__ == "__main__":
    main()
