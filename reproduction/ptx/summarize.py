"""Reconstruct archived PTX statements and check their evidence before tabulating."""

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from lark_kernels.frontend import translate
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec
from reproduction.ptx.run import MUTANTS

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(root):
    manifest = json.loads((root / "manifest.json").read_text())
    actual = {
        str(p.relative_to(root)): sha(p)
        for p in root.rglob("*")
        if p.is_file() and p.name != "manifest.json" and ".lake" not in p.parts
    }
    require(manifest == actual, "Archive manifest differs")
    report = json.loads((root / "results.json").read_text())
    require(report["status"] == "finished", "Study is unfinished")
    require(report["nvidia_execution"] is False and report["model_calls"] == 0, "Scope differs")
    require(report["original_paper_fully_reproduced"] is False, "Unexpected original-paper claim")
    for name, expected in report["source_files"].items():
        require(
            sha(REPO / name) == expected, "Run source differs; use its recorded revision: " + name
        )
    names = [r["case"] for r in report["certificates"]]
    require(sorted(names) == ["copy", "gemv", "relu", "vector_add"], "Fixture set differs")
    rows = []
    for row in report["certificates"]:
        name = row["case"]
        dest, fixture = root / "certificates" / name, ROOT / "cases" / name
        for f in ("kernel.ptx", "reference.py", "task.json"):
            require((dest / f).read_bytes() == (fixture / f).read_bytes(), "Fixture bytes differ")
        task = Task.read(dest / "task.json")
        tr = translate((dest / "kernel.ptx").read_text(), task)
        spec = read_spec((dest / "reference.py").read_text(), task)
        proposal = json.loads((dest / "proposal.json").read_text())
        require(
            (dest / "Main.lean").read_text() == certificate.render(task, tr, spec, proposal),
            "Archived theorem differs from immutable source-bound statement",
        )
        checked = json.loads((dest / "report.json").read_text())
        require(checked["status"] == "verified", "Certificate did not verify")
        for f, expected in checked["files"].items():
            require(sha(dest / f) == expected, "Certificate manifest differs")
        log = (dest / "independent-recheck.log").read_text()
        require(
            "LarkCertificate.kernel_eq_spec_pre" in log and "error:" not in log, "Recheck failed"
        )
        if "assembly" in row:
            require(row["assembly"]["returncode"] == 0, "Assembly failed")
            require(
                sha(dest / "assembled.cubin") == row["assembly"]["cubin_sha256"], "Cubin changed"
            )
        rows.append(
            {"case": name, "lowered_instructions": len(tr.program), "accesses": checked["accesses"]}
        )
    base = ROOT / "cases/vector_add"
    task = replace(Task.read(base / "task.json"), fuel=(32, 16, 16, 16))
    source = (base / "kernel.ptx").read_text()
    spec = read_spec((base / "reference.py").read_text(), task)
    require(sorted(m["name"] for m in report["mutants"]) == sorted(MUTANTS), "Mutant set differs")
    for row in report["mutants"]:
        dest = root / "mutants" / row["name"]
        before, after = MUTANTS[row["name"]]
        changed = source.replace(before, after)
        require((dest / "kernel.ptx").read_text() == changed, "Mutant source differs")
        tr = translate(changed, task)
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(certificate.DEFAULT_PROOFS),
        }
        require(
            (dest / "Main.lean").read_text() == certificate.render(task, tr, spec, proposal),
            "Mutant theorem differs",
        )
        log = (dest / "lean.log").read_text()
        require("error:" in log and "Lean timed out" not in log, "Direct Lean rejection missing")
        require(row["python_preflight_used"] is False, "Mutant did not bypass preflight")
    return {
        "status": "archived-statements-and-manifests-reconstructed",
        "original_paper_fully_reproduced": False,
        "nvidia_execution": False,
        "certificates": rows,
        "verified_certificates": len(rows),
        "independent_rechecks_recorded": len(rows),
        "assembled_sources": sum("assembly" in row for row in report["certificates"]),
        "direct_lean_rejections": len(report["mutants"]),
        "mutant_timeouts": 0,
        "fresh_lean_rechecks_by_this_summary": 0,
        "scope": "Reconstructs evidence from the completed study; use lark check for another Lean recheck. Independent tiny PTX fixtures, not original PTX/production kernels or hardware results.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, default=ROOT / "results/cpu-20261109")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.output.resolve().is_relative_to(args.run.resolve()):
        parser.error("fresh output outside the immutable study required")
    summary = audit(args.run)
    args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
