"""Fresh source-bound canonical-real native attention proofs and scoped controls.

Uses only the pinned local Mathlib dependency cache; no GPU or model calls.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_attention as native  # noqa: E402
from lark_kernels import real_backend  # noqa: E402
from lark_kernels.ir import lean_node  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_fp16"
TARGET = "LarkReal.NativeAttention"
NAMES = (
    "dot_fold_real", "score_value_real", "tile_denominator_real", "tile_numerator_real",
    "first_real_step", "next_real_step", "online_real_valid", "online_mass_positive",
    "processed_entries_dense", "online_dense_reference", "source_spec_dense", "correct",
)
GROUPS = (1, 3, 64, 65535)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def closure(module, found=None, external=None):
    found = set() if found is None else found
    external = set() if external is None else external
    if module in found:
        return found, external
    require(re.fullmatch(r"Lark(?:Real)?\.[A-Za-z0-9_]+", module), "Unexpected module: " + module)
    found.add(module)
    folder = "lean-real" if module.startswith("LarkReal.") else "lean"
    source = ROOT / folder / (module.replace(".", "/") + ".lean")
    for line in source.read_text().splitlines():
        if line.startswith("import "):
            for dependency in line.split()[1:]:
                if dependency.startswith(("Lark.", "LarkReal.")):
                    closure(dependency, found, external)
                else:
                    require(dependency == "Std" or dependency.startswith("Mathlib."), "Unexpected import: " + dependency)
                    external.add(dependency)
    return found, external


def check(cwd, command, dest, positive=True, timeout=600):
    before = time.monotonic()
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    log = result.stdout + result.stderr
    dest.write_text(log)
    if positive:
        require(result.returncode == 0 and "error:" not in log and "sorryAx" not in log, "Positive check failed: " + str(dest))
    else:
        require(result.returncode != 0 and "error:" in log and ("is false" in log or "⊢ False" in log),
                "Control did not reach its false claim: " + str(dest))
    return {"name": dest.stem, "expected_accepted": positive, "accepted": result.returncode == 0,
            "exit_code": result.returncode, "seconds": time.monotonic() - before, "timed_out": False}


def audit(log, name):
    entries = re.findall(r"^'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]$", log, re.M)
    require(len(entries) == 1, "Missing or ambiguous axiom audit: " + name)
    axioms = entries[0].split(", ") if entries[0] else []
    require(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose --output outside a Git checkout")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "source"
    project.mkdir()
    task = native.parse_task((CASE / "task.json").read_text())
    source = (CASE / "kernel.hip").read_bytes().decode()
    native.check_reference((CASE / "reference.py").read_text(), task)
    provenance = json.loads((HERE / "native-provenance.json").read_text())
    require(sha(CASE / "kernel.hip") == provenance["native_source_sha256"], "Native source changed")
    translated = native.translate(source, task)
    modules, external = closure(TARGET)
    for module in sorted(modules):
        folder = "lean-real" if module.startswith("LarkReal.") else "lean"
        name = module.replace(".", "/") + ".lean"
        dest = project / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / folder / name, dest)
    for name, contents in real_backend.configuration().items():
        (project / name).write_bytes(contents)
    globals_code = ", ".join(f"⟨.{b.role}, p.groups * {b.size // task.grid}⟩" for b in task.buffers)
    binding = f"""import {TARGET}
open LarkNonlinear LarkNativeAttention
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace NativeAttentionExport
def sourceProgram : List Instr := [
""" + ",\n".join(lean_node(i) for i in translated.program) + f"""
]
def sourceShared : List Nat := {[size for _, size in translated.shared]}
def sourceLocals : List Nat := {[size for _, size in translated.locals]}
def sourceLayout (p : Shape) : Layout := ⟨[{globals_code}], sourceShared, sourceLocals⟩
def sourceGeometry (p : Shape) : Geometry := ⟨p.groups, {task.block}, {task.warp}⟩
def sourceFuel : Fuel := ⟨{', '.join(str(x) for x in task.fuel)}⟩
theorem program_binding : sourceProgram = program := by decide
theorem layout_binding (p : Shape) : sourceLayout p = layout p := rfl
theorem geometry_binding (p : Shape) : sourceGeometry p = geometry p := rfl
theorem fuel_binding : sourceFuel = fuel := by decide
theorem source_bound_correct (p : Shape) :
    Correct LarkReal.ops (sourceLayout p) (sourceGeometry p) sourceFuel sourceProgram (LarkReal.NativeAttention.denseSpec p) := by
  rw [program_binding, layout_binding, geometry_binding, fuel_binding]
  exact LarkReal.NativeAttention.correct p
#print axioms source_bound_correct
end NativeAttentionExport
""" + "\n".join("#print axioms LarkReal.NativeAttention." + n for n in NAMES) + "\n"
    (project / "Main.lean").write_text(binding)
    for groups in GROUPS:
        data = json.loads((CASE / "task.json").read_text())
        for buffer in data["buffers"]:
            buffer["shape"][0] = groups
        data["launch"]["grid"] = groups
        require(native.parse_task(json.dumps(data)).grid == groups, "Specialization refused")
        (project / f"groups-{groups}.lean").write_text(f"""import Main
open LarkNonlinear LarkNativeAttention NativeAttentionExport
def checkedShape : Shape := ⟨{groups}, by decide, by decide⟩
theorem group_correct : Correct LarkReal.ops (sourceLayout checkedShape) (sourceGeometry checkedShape)
    sourceFuel sourceProgram (LarkReal.NativeAttention.denseSpec checkedShape) := source_bound_correct checkedShape
#print axioms group_correct
""")
    controls = {
        "removed-final-halt": """import Main
open LarkNativeAttention NativeAttentionExport
example : sourceProgram.dropLast = program := by decide
""",
        "wrong-private-layout": """import Main
open NativeAttentionExport
example : sourceLocals = [4] := by decide
""",
        "wrong-native-block-size": """import Main
open NativeAttentionExport
example : sourceGeometry ⟨1, by decide, by decide⟩ = ⟨1, 64, 64⟩ := by decide
""",
        "wrong-dense-output-value": """import Main
open LarkNativeAttention LarkReal.NativeAttention
example (input : Nat → Nat → ℝ) (t qi col : Nat)
    (hv : LarkReal.OnlineSoftmax.reference (denseEntries input t qi) col = 0) :
    (onlineValues LarkReal.ops input 4 t qi).stored col = 1 := by
  rw [online_dense_reference, hv]
  norm_num
""",
    }
    for name, content in controls.items():
        (project / (name + ".lean")).write_text(content)
    frozen = project / "native-source"
    frozen.mkdir()
    for path in sorted(CASE.iterdir()):
        if path.is_file():
            shutil.copyfile(path, frozen / path.name)
    shutil.copyfile(HERE / "native-provenance.json", frozen / "native-provenance.json")
    shutil.copyfile(HERE / "upstream/LICENSE", frozen / "UPSTREAM-LICENSE")
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "README.md").write_text(
        "# Canonical-real native attention certificate\n\n"
        "Lean 4.19.0 and the exact locked Mathlib revision are required. Run `lake update`, fetch the Mathlib cache, then `lake build`.\n"
        "Run `lake env lean groups-<n>.lean` for n=1,3,64,65535. The four other top-level Lean files intentionally fail.\n"
        "The universal theorem covers all group counts 1..65535, all inputs and outside memory, actual native launch/race freedom and dense real SDPA.\n"
        "Half casts are identities only in this real interpretation. No IEEE equivalence, error bound or original-paper completion is claimed.\n")
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
    _, seeds = real_backend.dependencies()
    packages = project / ".lake/packages"
    packages.mkdir(parents=True)
    for name, path in seeds.items():
        (packages / name).symlink_to(path, target_is_directory=True)
    records = [check(project, ["lake", "build"], out / "build.log")]
    records.append(check(project, ["lake", "env", "lean", "Main.lean"], out / "main.log"))
    for groups in GROUPS:
        records.append(check(project, ["lake", "env", "lean", f"groups-{groups}.lean"], out / f"groups-{groups}.log"))
    for name in controls:
        records.append(check(project, ["lake", "env", "lean", name + ".lean"], out / (name + ".log"), False))
    main_log = (out / "main.log").read_text()
    audits = {name: audit(main_log, "LarkReal.NativeAttention." + name) for name in NAMES}
    audits["source_bound_correct"] = audit(main_log, "NativeAttentionExport.source_bound_correct")
    for groups in GROUPS:
        audits[f"groups-{groups}"] = audit((out / f"groups-{groups}.log").read_text(), "group_correct")
    report = {
        "schema": 1, "status": "native-canonical-real-whole-launch-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "groups": {"min": 1, "max": 65535}, "export_groups": list(GROUPS), "block": 32, "warp": 64,
        "local_lean_modules": len(modules), "local_real_modules": sum(m.startswith("LarkReal.") for m in modules),
        "direct_external_imports": sorted(external), "mathlib_revision": real_backend.MATHLIB,
        "source_sha256": sha(CASE / "kernel.hip"), "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_certificates": len(GROUPS), "parameterized_source_certificate": True,
        "whole_kernel_execution_proved": True, "whole_kernel_race_freedom_proved": True,
        "source_reference_equality_proved": True, "canonical_dense_reference_equality_proved": True,
        "all_outputs_extracted_proved": True, "all_online_denominators_positive_proved": True,
        "storage_cast_interpretation": "identity in the canonical-real interpretation only",
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "gpu_trials": 0, "model_calls": 0,
        "axioms": audits, "false_claims_rejected": len(controls), "fresh_standalone_build": True, "checks": records,
    }
    write(out / "results.json", report)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: report[k] for k in ("status", "local_lean_modules", "source_certificates", "false_claims_rejected")}))


if __name__ == "__main__":
    main()
