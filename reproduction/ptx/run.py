"""Export/recheck four independent PTX certificates and four direct Lean controls."""

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from lark_kernels.frontend import translate
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
MUTANTS = {
    "wrong-arithmetic": ("add.rn.f32", "sub.rn.f32"),
    "conflicting-output": ("%rd2, %rd3", "%rd2, 0"),
    "misaligned-bytes": ("%r4, 4", "%r4, 2"),
    "skipped-predicate": (
        "setp.ge.u32 %p0, %r4, 3;",
        "bra skip; setp.ge.u32 %p0, %r4, 3; skip:",
    ),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--ptxas", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("fresh output directory required")
    out = args.output
    out.mkdir(parents=True)
    summary = {
        "schema": 1,
        "original_paper_fully_reproduced": False,
        "status": "running",
        "nvidia_execution": False,
        "model_calls": 0,
        "certificates": [],
        "mutants": [],
        "source_files": {
            str(p.relative_to(REPO)): sha(p)
            for p in [
                Path(__file__),
                *(REPO / "lark_kernels").glob("*.py"),
                REPO / "lean/Lark/Model.lean",
                *sorted((ROOT / "cases").glob("*/*")),
            ]
            if p.is_file()
        },
    }
    if args.ptxas:
        version = subprocess.run(
            [str(args.ptxas), "--version"], capture_output=True, text=True, check=True
        )
        summary["assembler"] = {
            "path": str(args.ptxas),
            "sha256": sha(args.ptxas),
            "version": version.stdout + version.stderr,
            "scope": "Source assembly only; cubins are not executed",
        }
    for case in sorted((ROOT / "cases").iterdir()):
        dest = out / "certificates" / case.name
        start = time.monotonic()
        report = certificate.verify(
            case / "kernel.ptx",
            case / "reference.py",
            case / "task.json",
            dest,
            lean=args.lean,
            timeout=150,
        )
        if report["status"] != "verified":
            raise RuntimeError("Certificate did not verify: " + case.name)
        log = certificate.check(dest, lean=args.lean, timeout=150)
        (dest / "independent-recheck.log").write_text(log)
        record = {
            "case": case.name,
            "status": "verified-and-independently-rechecked",
            "accesses": report["accesses"],
            "elapsed_seconds": time.monotonic() - start,
        }
        if args.ptxas:
            command = [
                str(args.ptxas),
                "--gpu-name=sm_80",
                "--verbose",
                str(case / "kernel.ptx"),
                "-o",
                str(dest / "assembled.cubin"),
            ]
            result = subprocess.run(command, capture_output=True, text=True)
            (dest / "assembly.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError("Assembler rejected source: " + case.name)
            record["assembly"] = {
                "command": command,
                "returncode": result.returncode,
                "cubin_sha256": sha(dest / "assembled.cubin"),
            }
        summary["certificates"].append(record)
        write(out / "results.json", summary)
        print(case.name, record["status"], flush=True)
    base = ROOT / "cases/vector_add"
    task = replace(Task.read(base / "task.json"), fuel=(32, 16, 16, 16))
    source = (base / "kernel.ptx").read_text()
    spec = read_spec((base / "reference.py").read_text(), task)
    for name, (before, after) in MUTANTS.items():
        if source.count(before) != 1:
            raise RuntimeError("Mutation anchor differs")
        dest = out / "mutants" / name
        dest.mkdir(parents=True)
        changed = source.replace(before, after)
        (dest / "kernel.ptx").write_text(changed)
        tr = translate(changed, task)
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(certificate.DEFAULT_PROOFS),
        }
        (dest / "Main.lean").write_text(certificate.render(task, tr, spec, proposal))
        start = time.monotonic()
        accepted, log = certificate.run_lean(dest, args.lean, 60)
        (dest / "lean.log").write_text(log)
        if accepted or "error:" not in log or "Lean timed out" in log:
            raise RuntimeError("Direct Lean negative control failed: " + name)
        summary["mutants"].append(
            {
                "name": name,
                "status": "rejected-directly-by-lean",
                "python_preflight_used": False,
                "elapsed_seconds": time.monotonic() - start,
                "source_sha256": sha(dest / "kernel.ptx"),
            }
        )
        write(out / "results.json", summary)
        print(name, "rejected directly by Lean", flush=True)
    summary["status"] = "finished"
    summary["scope"] = (
        "Four independent tiny float32 PTX 8.0/sm_80 fixtures; abstract exact scalar operations, bounded launches, trusted reader/lowering. Four independent negative controls are not the paper's original mutants. No NVIDIA execution, original PTX/production kernels, timings, IEEE claims or model pass-rate results."
    )
    write(out / "results.json", summary)
    write(
        out / "manifest.json",
        {
            str(p.relative_to(out)): sha(p)
            for p in sorted(out.rglob("*"))
            if p.is_file() and p.name != "manifest.json" and ".lake" not in p.parts
        },
    )


if __name__ == "__main__":
    main()
