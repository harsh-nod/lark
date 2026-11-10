"""Verify/recheck five full-wave HIP shuffle kernels and direct Lean mutations."""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate, collective
from lark_kernels.ir import Refusal, Task
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
MUTANTS = {
    "wrong-broadcast": ("broadcast8", "value, 1, 8", "value, 2, 8"),
    "wrong-xor": ("xor8", "value, 1, 8", "value, 2, 8"),
    "wrong-direction": ("up8", "__shfl_up", "__shfl_down"),
    "invalid-source-lane": ("reverse", "63 - i", "62 - i"),
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
    args.output.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1,
        "status": "running",
        "source_files": source_files(),
        "original_paper_fully_reproduced": False,
        "model_calls": 0,
        "certificates": [],
        "mutants": [],
    }
    for case in sorted((ROOT / "cases").iterdir()):
        dest = args.output / "certificates" / case.name
        start = time.monotonic()
        result = collective.verify(
            case / "kernel.hip",
            case / "reference.py",
            case / "task.json",
            dest,
            lean=args.lean,
            timeout=150,
        )
        if result["status"] != "verified":
            raise RuntimeError("Certificate did not verify: " + case.name)
        (dest / "independent-recheck.log").write_text(
            certificate.check(dest, lean=args.lean, timeout=150)
        )
        report["certificates"].append(
            {
                "case": case.name,
                "status": "verified-and-rechecked",
                "accesses": result["accesses"],
                "elapsed_seconds": time.monotonic() - start,
            }
        )
        write(args.output / "results.json", report)
        print(case.name, "verified and rechecked", flush=True)
    for name, (case, before, after) in MUTANTS.items():
        fixture = ROOT / "cases" / case
        task = Task.read(fixture / "task.json")
        source = (fixture / "kernel.hip").read_text()
        if source.count(before) != 1:
            raise RuntimeError("Mutation anchor differs")
        changed = source.replace(before, after)
        spec = read_spec((fixture / "reference.py").read_text(), task)
        tr = collective.translate(changed, task)
        try:
            trace = collective.Machine(task, tr).run().trace
        except Refusal:
            trace = []
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": collective.default_proofs(task, tr, spec, trace),
        }
        dest = args.output / "mutants" / name
        dest.mkdir(parents=True)
        (dest / "kernel.hip").write_text(changed)
        write(dest / "proposal.json", proposal)
        (dest / "Main.lean").write_text(collective.render(task, tr, spec, proposal))
        start = time.monotonic()
        accepted, log = certificate.run_lean(dest, args.lean, 90)
        (dest / "lean.log").write_text(log)
        if accepted or "error:" not in log or "Lean timed out" in log:
            raise RuntimeError("Direct Lean negative control failed: " + name)
        report["mutants"].append(
            {
                "name": name,
                "case": case,
                "status": "rejected-directly-by-lean",
                "python_preflight_used": False,
                "elapsed_seconds": time.monotonic() - start,
            }
        )
        write(args.output / "results.json", report)
        print(name, "rejected directly by Lean", flush=True)
    if source_files() != report["source_files"]:
        raise RuntimeError("Study source changed during execution")
    report["status"] = "finished"
    report["scope"] = (
        "Five independent full-wave64 float32 HIP transport kernels, four direct Lean controls. "
        "Universal input/outside-state launch completion, RF and output equality under the "
        "opt-in snapshot-register machine. Shuffles add no memory ordering. Source/operation "
        "correspondence and phase-reduction metatheory remain trusted. Not original kernels, "
        "partial participation, tensor cores, NVIDIA execution or paper pass-rate results."
    )
    write(args.output / "results.json", report)
    write(
        args.output / "manifest.json",
        {
            str(f.relative_to(args.output)): sha(f)
            for f in sorted(args.output.rglob("*"))
            if f.is_file() and f.name != "manifest.json" and ".lake" not in f.parts
        },
    )


if __name__ == "__main__":
    main()
