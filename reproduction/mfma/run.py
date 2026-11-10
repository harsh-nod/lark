"""Verify/recheck a full MFMA tile and reject four source/reference mutations in Lean."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, mfma
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
MUTANTS = {
    "wrong-a-stride": ("kernel.hip", "(lane % 16) * 16", "(lane % 16) * 8"),
    "wrong-b-register": ("kernel.hip", "left, right, acc", "left, left, acc"),
    "wrong-output-component": ("kernel.hip", "= acc[0];", "= acc[1];"),
    "dropped-accumulator-reference": ("reference.py", " + c", ""),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def source_files():
    paths = [
        Path(__file__),
        *(REPO / "lark_kernels").glob("*.py"),
        *(REPO / "lean/Lark").glob("*.lean"),
        *sorted((ROOT / "cases").glob("*/*")),
    ]
    return {str(p.relative_to(REPO)): sha(p) for p in paths if p.is_file()}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "status": "running",
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "source_files": source_files(),
        "certificates": [],
        "mutants": [],
    }
    case = ROOT / "cases/gemm16"
    dest = out / "certificates/gemm16"
    start = time.monotonic()
    result = mfma.verify(
        case / "kernel.hip",
        case / "reference.py",
        case / "task.json",
        dest,
        lean=args.lean,
        timeout=150,
    )
    if result["status"] != "verified":
        raise RuntimeError("MFMA certificate did not verify")
    (dest / "independent-recheck.log").write_text(
        certificate.check(dest, lean=args.lean, timeout=150)
    )
    report["certificates"].append(
        {
            "case": "gemm16",
            "status": "verified-and-rechecked",
            "accesses": result["accesses"],
            "elapsed_seconds": time.monotonic() - start,
        }
    )
    write(out / "results.json", report)
    print("gemm16 verified and independently rechecked", flush=True)
    task = Task.read(case / "task.json")
    for name, (filename, before, after) in MUTANTS.items():
        changed = out / "mutants" / name
        changed.mkdir(parents=True)
        for f in ("kernel.hip", "reference.py", "task.json"):
            shutil.copyfile(case / f, changed / f)
        source = (changed / filename).read_text()
        if before not in source:
            raise RuntimeError("Mutation anchor differs")
        (changed / filename).write_text(source.replace(before, after))
        tr = mfma.translate((changed / "kernel.hip").read_bytes().decode(), task)
        spec = read_spec((changed / "reference.py").read_text(), task)
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(mfma.DEFAULT_PROOFS),
        }
        write(changed / "proposal.json", proposal)
        (changed / "Main.lean").write_text(mfma.render(task, tr, spec, proposal))
        start = time.monotonic()
        accepted, log = certificate.run_lean(changed, args.lean, 90)
        (changed / "lean.log").write_text(log)
        if accepted or "error:" not in log or "Lean timed out" in log:
            raise RuntimeError("Direct Lean control failed: " + name)
        report["mutants"].append(
            {
                "name": name,
                "status": "rejected-directly-by-lean",
                "python_preflight_used": False,
                "elapsed_seconds": time.monotonic() - start,
                "channel": "fixed-template-program-equality"
                if filename == "kernel.hip"
                else "independent-reference-equality",
            }
        )
        write(out / "results.json", report)
        print(name, "rejected directly by Lean", flush=True)
    if source_files() != report["source_files"]:
        raise RuntimeError("Study sources changed during execution")
    report.update(
        status="finished",
        scope=(
            "Independent one-wave 16x16 half-input/float-output native MFMA kernel with modifiers (0,0,0). "
            "Whole-launch completion, race freedom and all 256 outputs for arbitrary inputs/outside memory, "
            "under exact abstract scalar/half operations and the snapshot-register instruction definition. "
            "Four controls bypass Python preflight; three fail fixed-program equality and one fails reference equality. "
            "Not original kernels/mutants, partial masks, other shapes/modifiers, IEEE accumulation semantics or NVIDIA results."
        ),
    )
    write(out / "results.json", report)
    write(
        out / "manifest.json",
        {
            str(f.relative_to(out)): sha(f)
            for f in sorted(out.rglob("*"))
            if f.is_file() and f.name != "manifest.json" and ".lake" not in f.parts
        },
    )


if __name__ == "__main__":
    main()
