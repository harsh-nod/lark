"""Check the source-bound seeded-inout real profile and meaningful refusals.

Uses the pinned optional Mathlib cache; makes no model calls or GPU launches.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_fused_rmsnorm_certificate as native  # noqa: E402
from lark_kernels import real_backend  # noqa: E402
from lark_kernels.certificate import check, lean_binary  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_16384"
SOURCE_SHA = "c297c1842c1a4d2d9be2265aa0d03da759dda22f555947e3483eccb486e5f59e"
ROWS = (1, 3, 64, 255)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def audits(log):
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    result = dict(entries)
    require(len(result) == len(entries), "Repeated axiom audit")
    for name, ax in entries:
        require(set(a.strip() for a in ax.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean")
    args = parser.parse_args()
    out = args.output.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    require(sha(CASE / "kernel.hip") == SOURCE_SHA, "Native source changed")
    out.mkdir(parents=True, exist_ok=False)
    lean = lean_binary(args.lean)
    libraries = native.libraries()
    checks = []

    def record(name, accepted, expected, before):
        require(accepted is expected, "Unexpected acceptance: " + name)
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "seconds": time.monotonic() - before, "timed_out": False})

    baseline = None
    for rows in ROWS:
        data = json.loads((CASE / "task.json").read_text())
        data["launch"]["grid"] = rows
        for buffer in data["buffers"][:2]:
            buffer["shape"][0] = rows
        task = out / f"task-{rows}.json"
        write(task, data)
        dest = out / f"rows-{rows}"
        before = time.monotonic()
        report = native.verify(CASE / "kernel.hip", CASE / "reference.py", task, dest, lean=lean, timeout=600)
        record(f"rows-{rows}", report["status"] == "verified", True, before)
        require(report["output_elements"] == 2 * rows * 16384, "Both output buffers not counted")
        before = time.monotonic()
        log = check(dest, lean=lean, timeout=600)
        (out / f"recheck-rows-{rows}.log").write_text(log)
        record(f"recheck-rows-{rows}", True, True, before)
        if rows == 1:
            baseline = dest

    main_source = (baseline / "Main.lean").read_text()
    # These controls must reach Lean. Their source parses normally and has exact
    # readback; the fixed source theorem rejects the changed emitted program.
    source = (CASE / "kernel.hip").read_text()
    source_controls = {
        "source-missing-barrier": source.replace("__syncthreads();", "", 1),
        "source-wrong-xor": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
        "source-wrong-weight": source.replace("weight[output_column]", "weight[0]"),
        "source-rounded-shared-read": source.replace("float value = unrounded[output_column];",
                                                      "float value = __half2float(residual[output_address]);"),
    }
    controls_dir = out / "controls"
    controls_dir.mkdir()
    for name, changed in source_controls.items():
        require(changed != source, "Vacuous mutation: " + name)
        kernel = controls_dir / (name + ".hip")
        kernel.write_text(changed)
        before = time.monotonic()
        report = native.verify(kernel, CASE / "reference.py", CASE / "task.json", controls_dir / name,
                               lean=lean, timeout=600)
        require("program_data" in report["axiom_audit"] and "is false" in report["axiom_audit"]
                and "maximum recursion" not in report["axiom_audit"]
                and "maximum number of heartbeats" not in report["axiom_audit"], "Wrong source rejection gate: " + name)
        record(name, report["status"] == "verified", False, before)

    direct_controls = {
        "omitted-residual-initialization": main_source.replace("def mutableBuffers : List Nat := [0, 1]",
                                                                 "def mutableBuffers : List Nat := [0]", 1),
        "wrong-source-block-fuel": main_source.replace("def fuel : Fuel := ⟨512, 8, 3, 1⟩",
                                                      "def fuel : Fuel := ⟨512, 8, 2, 1⟩", 1).replace(
            "theorem fuel_data : fuel = LarkNativeFusedRmsNorm.fuel := by rfl",
            "theorem fuel_data : fuel = LarkNativeFusedRmsNorm.fuel := by decide", 1),
        "wrong-residual-reference": """import LarkReal.NativeFusedRmsNorm
open LarkReal.NativeFusedRmsNorm
example : canonical_residual (fun b _ => if b = 0 then 1 else 2) 0 0 = 2 := by
  norm_num [canonical_residual]
""",
        "missing-second-extraction": """import LarkReal.NativeFusedRmsNorm
open LarkReal.NativeFusedRmsNorm
example (input : Nat → Nat → ℝ) :
    (canonical_spec ⟨1, by decide, by decide⟩ input).length = 16384 := by
  simp [canonical_spec]
""",
    }
    for name, changed in direct_controls.items():
        require(changed != main_source, "Vacuous mutation: " + name)
        (controls_dir / (name + ".lean")).write_text(changed)
        before = time.monotonic()
        accepted, log = native.validate_main(changed.encode(), libraries, lean, 600)
        (out / (name + ".log")).write_text(log)
        require("error:" in log and ("is false" in log or "⊢ False" in log)
                and "maximum" not in log and "Stack overflow" not in log,
                "Wrong direct rejection gate: " + name)
        record(name, accepted, False, before)

    reference = (CASE / "reference.py").read_text()
    for name, changed in {
        "reference-missing-residual": reference.replace("return output, x.half()", "return output"),
        "reference-old-residual": reference.replace("return output, x.half()", "return output, residual"),
        "reference-wrong-axis": reference.replace("dim=1", "dim=0"),
        "reference-wrong-epsilon": reference.replace("1e-5", "1e-4"),
    }.items():
        before = time.monotonic()
        try:
            native.prepare(source, changed, (CASE / "task.json").read_text())
        except Refusal as error:
            (out / (name + ".log")).write_text(str(error) + "\n")
            record(name, False, False, before)
        else:
            raise ValueError("Changed reference accepted: " + name)

    # Rehash each changed file in report.json, so rejection cannot be explained
    # by a stale outer digest. The fixed source/model/statement and scope gates
    # must still refuse it.
    for name, filename, transform in (
        ("rehashed-main", "Main.lean", lambda text: text.replace("def mutableBuffers : List Nat := [0, 1]",
                                                                  "def mutableBuffers : List Nat := [0]", 1)),
        ("rehashed-model", "Lark/InOutPartition.lean", lambda text: text + "\n-- changed pinned model\n"),
        ("rehashed-reference", "reference.py", lambda text: text.replace("return output, x.half()", "return output, residual")),
        ("rehashed-source", "kernel.hip", lambda text: text.replace("weight[output_column]", "weight[0]")),
        ("invented-ieee-proof", None, None),
        ("invented-paper-completion", None, None),
        ("missing-inout-proof", None, None),
    ):
        dest = controls_dir / name
        shutil.copytree(baseline, dest)
        report = json.loads((dest / "report.json").read_text())
        if filename:
            path = dest / filename
            path.write_text(transform(path.read_text()))
            report["files"][filename] = sha(path)
            if filename in report["model_hashes"]:
                report["model_hashes"][filename] = sha(path)
        elif name == "invented-ieee-proof":
            report["ieee_equivalence_proved"] = True
        elif name == "invented-paper-completion":
            report["original_paper_fully_reproduced"] = True
        else:
            report["seeded_inout_proved"] = False
        write(dest / "report.json", report)
        before = time.monotonic()
        try:
            check(dest, lean=lean, timeout=600)
        except Refusal as error:
            (out / (name + ".log")).write_text(str(error) + "\n")
            record(name, False, False, before)
        else:
            raise ValueError("Rehashed tamper accepted: " + name)

    cache, _ = real_backend.prepare(libraries, lean, 600, target=native.TARGET)
    shutil.copyfile(cache / "build.log", out / "fresh-library-build.log")
    library_audits = audits((out / "fresh-library-build.log").read_text())
    main_audits = audits((baseline / "lean-1.log").read_text())
    require("LarkReal.NativeFusedRmsNorm.correct" in library_audits
            and "LarkCertificate.kernel_eq_spec_pre" in main_audits, "Principal theorem audits absent")
    project = out / "source"
    shutil.copytree(baseline, project)
    for name in ("report.json", "lean-1.log"):
        (project / name).unlink()
    frozen = project / "lark_kernels"
    frozen.mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, frozen / path.name)
    (project / "validate_source.py").write_text('''from pathlib import Path
from lark_kernels import native_fused_rmsnorm_certificate as native
root = Path(__file__).resolve().parent
contract, translation = native.prepare(*((root / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))
assert (root / "Main.lean").read_text() == native.render(contract, translation)
print("Frozen reader, exact readback, two-output reference and source-to-Main binding passed.")
''')
    for rows in ROWS[1:]:
        (project / f"rows-{rows}.lean").write_bytes((out / f"rows-{rows}/Main.lean").read_bytes())
    for name in direct_controls:
        shutil.copyfile(controls_dir / (name + ".lean"), project / (name + ".lean"))
    for name in source_controls:
        shutil.copyfile(controls_dir / name / "Main.lean", project / (name + ".lean"))
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    shutil.copyfile(HERE / "upstream/FLASHINFER_LICENSE", project / "UPSTREAM-LICENSE")
    (project / "README.md").write_text(
        "Source replay: python3 validate_source.py. Fresh proof: lake build.\n"
        "Requires Lean4.19.0 and the exact locked Mathlib dependencies/cache.\n"
        "rows-{3,64,255}.lean specialize the universal rows1..255 theorem.\n"
        "The other top-level Lean files intentionally fail.\n"
        "The whole seeded-inout launch, actual trace race freedom and both real reference buffers are proved.\n"
        "Half conversions are identities here; no IEEE error bound or original-paper completion is claimed.\n")
    paths = sorted(p for p in project.rglob("*") if p.is_file())
    write(out / "source-manifest.json", {str(p.relative_to(project)): sha(p) for p in paths})
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for path in paths:
            info = archive.gettarinfo(str(path), arcname=str(path.relative_to(project)))
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ""
            with path.open("rb") as stream:
                archive.addfile(info, stream)
    shutil.copyfile(Path(__file__), out / "checker.py")
    result = {
        "schema": 1, "status": "native-inout-canonical-real-whole-launch-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "model_profile": native.PROFILE, "rows": {"min": 1, "max": 255}, "export_rows": list(ROWS),
        "block": 1024, "physical_warp": 64, "logical_warp": 32,
        "source_sha256": SOURCE_SHA, "source_archive_sha256": sha(out / "source.tar.gz"),
        "local_lean_modules": len(libraries), "local_real_modules": 2,
        "mathlib_revision": real_backend.MATHLIB, "source_certificates": len(ROWS),
        "parameterized_source_certificate": True, "whole_kernel_execution_proved": True,
        "actual_trace_race_freedom_proved": True, "seeded_inout_proved": True,
        "both_output_buffers_extracted": True, "source_reference_equality_proved": True,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
        "library_axiom_audits": library_audits, "main_axiom_audits": main_audits,
        "false_claims_rejected": sum(not c["expected_accepted"] for c in checks), "checks": checks,
    }
    write(out / "results.json", result)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: result[k] for k in ("status", "source_certificates", "false_claims_rejected")}))


if __name__ == "__main__":
    main()
