"""Check the source-bound SGLang real profile and meaningful refusals.

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
from lark_kernels import native_sglang_rmsnorm_certificate as native  # noqa: E402
from lark_kernels import real_backend  # noqa: E402
from lark_kernels.certificate import check, lean_binary  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_fixed"
SOURCE_SHA = "1758b5db41b411172c39b9d812121f1a4ba2f254f3643ccd55e89f8aac579257"
ROWS = (1, 3, 64, 131072)


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
        require(report["output_elements"] == rows * 16384, "Output buffer not counted")
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
        "source-unguarded-partial-store": source.replace("if (lane == 0) {\npartial[warp] = sum;\n}", "partial[warp] = sum;"),
        "source-missing-first-barrier": source.replace("__syncthreads();", "", 1),
        "source-missing-second-barrier": "".join(source.rsplit("__syncthreads();", 1)),
        "source-wrong-first-xor": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
        "source-wrong-second-xor": source.replace("__shfl_xor(block_sum, 16, 32)", "__shfl_xor(block_sum, 8, 32)", 1),
        "source-wrong-input-cache-address": source.replace("input[input_address]", "input[0]"),
        "source-wrong-weight-cache-address": source.replace("weight[weight_column]", "weight[0]"),
        "source-reordered-pair-add": source.replace("sum = sum + pair_square;", "sum = pair_square + sum;"),
        "source-aliased-output-cache": source.replace("output_values[output_slot + 1]", "output_values[output_slot]"),
        "source-wrong-output-address": source.replace("output[store_address]", "output[0]"),
        "source-wrong-epsilon": source.replace("mean + 0.00001f", "mean + 0.0001f"),
        "source-wrong-logical-width": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 16, 64)", 1),
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
        "wrong-source-block-fuel": main_source.replace("def fuel : Fuel := ⟨512, 8, 3, 1⟩",
                                                      "def fuel : Fuel := ⟨512, 8, 2, 1⟩", 1).replace(
            "theorem fuel_data : fuel = LarkNativeSglangRmsNorm.fuel := by rfl",
            "theorem fuel_data : fuel = LarkNativeSglangRmsNorm.fuel := by decide", 1),
        "wrong-private-half-layout": main_source.replace("[16, 16, 16]", "[16, 16, 15]", 1).replace(
            "theorem layout_data : layout = LarkNativeSglangRmsNorm.layout shape := by rfl",
            "theorem layout_data : layout = LarkNativeSglangRmsNorm.layout shape := by decide", 1),
        "wrong-guarded-halt-pc": """import LarkReal.NativeSglangRmsNorm
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : (program true)[108]? = some (.scalar .halt) := by decide
""",
        "wrong-square-reference": """import LarkReal.NativeSglangRmsNorm
open LarkReal.NativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : rowSquare (fun _ _ => (2 : ℝ)) 0 0 = 2 := by norm_num [rowSquare]
""",
        "wrong-output-length": """import LarkReal.NativeSglangRmsNorm
open LarkReal.NativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example (input : Nat → Nat → ℝ) :
    (canonical_spec ⟨1, by decide, by decide⟩ input).length = 16383 := by
  simp [canonical_spec]
""",
        "wrong-first-barrier-pc": """import LarkReal.NativeSglangRmsNorm
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : (program true)[55]? = some (.scalar (.barrier .block)) := by decide
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
        "reference-wrong-axis": reference.replace("dim=1", "dim=0"),
        "reference-wrong-epsilon": reference.replace("1e-5", "1e-4"),
        "reference-missing-weight": reference.replace("weight.float()", "1.0"),
        "reference-double-output": reference.replace("return (", "return input, ("),
    }.items():
        require(changed != reference, "Vacuous reference mutation: " + name)
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
        ("rehashed-main", "Main.lean", lambda text: text.replace("def fuel : Fuel := ⟨512, 8, 3, 1⟩",
                                                               "def fuel : Fuel := ⟨512, 8, 2, 1⟩", 1)),
        ("rehashed-model", "Lark/NativeSglangRmsNormGrid.lean", lambda text: text + "\n-- changed pinned model\n"),
        ("rehashed-reference", "reference.py", lambda text: text.replace("dim=1", "dim=0")),
        ("rehashed-source", "kernel.hip", lambda text: text.replace("weight[weight_column]", "weight[0]")),
        ("rehashed-translation", "translation.json", lambda text: text[:-2] + ', "forged": true}\n'),
        ("rehashed-configuration", "lake-manifest.json", lambda text: text + " "),
        ("invented-ieee-proof", None, None),
        ("invented-error-bound", None, None),
        ("invented-paper-completion", None, None),
        ("missing-whole-launch", None, None),
        ("missing-reference-proof", None, None),
        ("boolean-row-count", None, None),
        ("wrong-output-count", None, None),
        ("wrong-private-cache-count", None, None),
        ("wrong-private-cell-count", None, None),
        ("boolean-schema", None, None),
        ("invented-unguarded-proof", None, None),
        ("unknown-report-field", None, None),
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
        else:
            key, value = {
                "invented-ieee-proof": ("ieee_equivalence_proved", True),
                "invented-error-bound": ("floating_point_error_bound_proved", True),
                "invented-paper-completion": ("original_paper_fully_reproduced", True),
                "missing-whole-launch": ("whole_launch_proved", False),
                "missing-reference-proof": ("source_reference_equality_proved", False),
                "boolean-row-count": ("rows", True),
                "wrong-output-count": ("output_elements", 16383),
                "wrong-private-cache-count": ("private_half_caches", 2),
                "wrong-private-cell-count": ("private_half_cells_per_thread", 32),
                "boolean-schema": ("schema", True),
                "invented-unguarded-proof": ("unguarded_correctness_proved", True),
                "unknown-report-field": ("unsupported_extra_field", False),
            }[name]
            report[key] = value
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
    require(len(libraries) == 88 and len(library_audits) == 750 and len(main_audits) == 8,
            "Unexpected complete real proof closure")
    require("LarkReal.NativeSglangRmsNorm.correct" in library_audits
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
from lark_kernels import native_sglang_rmsnorm_certificate as native
root = Path(__file__).resolve().parent
contract, translation = native.prepare(*((root / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))
assert (root / "Main.lean").read_text() == native.render(contract, translation)
print("Frozen reader, exact readback, single-output reference and source-to-Main binding passed.")
''')
    for rows in ROWS[1:]:
        (project / f"rows-{rows}.lean").write_bytes((out / f"rows-{rows}/Main.lean").read_bytes())
    for name in direct_controls:
        shutil.copyfile(controls_dir / (name + ".lean"), project / (name + ".lean"))
    for name in source_controls:
        shutil.copyfile(controls_dir / name / "Main.lean", project / (name + ".lean"))
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    shutil.copyfile(HERE / "upstream/LICENSE", project / "UPSTREAM-LICENSE")
    (project / "README.md").write_text(
        "Source replay: python3 validate_source.py. Fresh proof: lake build.\n"
        "Requires Lean4.19.0 and the exact locked Mathlib dependencies/cache.\n"
        "rows-{3,64,131072}.lean specialize the universal rows1..131072 theorem.\n"
        "The other top-level Lean files intentionally fail.\n"
        "The guarded whole native launch, actual trace race freedom and dense real reference output are proved.\n"
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
        "schema": 1, "status": "native-sglang-canonical-real-whole-launch-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "model_profile": native.PROFILE, "rows": {"min": 1, "max": 131072}, "export_rows": list(ROWS),
        "block": 1024, "physical_warp": 64, "logical_warp": 32,
        "source_sha256": SOURCE_SHA, "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_manifest_sha256": sha(out / "source-manifest.json"),
        "local_lean_modules": len(libraries), "local_real_modules": 4,
        "mathlib_revision": real_backend.MATHLIB, "source_certificates": len(ROWS),
        "parameterized_source_certificate": True, "whole_kernel_execution_proved": True,
        "actual_trace_race_freedom_proved": True, "source_reference_equality_proved": True,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
        "library_axiom_audits": library_audits, "main_axiom_audits": main_audits,
        "export_axiom_audits": {str(rows): audits((out / f"rows-{rows}/lean-1.log").read_text()) for rows in ROWS},
        "false_lean_claims_rejected": len(source_controls) + len(direct_controls),
        "false_claims_rejected": sum(not c["expected_accepted"] for c in checks), "checks": checks,
    }
    write(out / "results.json", result)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: result[k] for k in ("status", "source_certificates", "false_claims_rejected")}))


if __name__ == "__main__":
    main()
