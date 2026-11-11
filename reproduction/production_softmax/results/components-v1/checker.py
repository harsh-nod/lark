"""Check full-source identity, ownership lemmas and instruction-level race evidence.

Whole-kernel execution, actual-trace universal classification and reference
equivalence are separate obligations. This stage issues no source certificate.
"""

import argparse
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
from lark_kernels import collective, native_softmax as native  # noqa: E402
from lark_kernels.ir import lean_list  # noqa: E402
from reproduction.production_softmax.prepare import source as expected_source  # noqa: E402

HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxWitness"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modules(name, found):
    if name in found:
        return
    require(re.fullmatch(r"Lark\.[A-Za-z0-9_]+", name), "Unexpected module: " + name)
    found.add(name)
    for line in (ROOT / "lean" / (name.replace(".", "/") + ".lean")).read_text().splitlines():
        if line.startswith("import "):
            for dependency in line.split()[1:]:
                if dependency.startswith("Lark."):
                    modules(dependency, found)
                else:
                    require(dependency == "Std", "Unexpected external dependency")


def statement(original, fixed, task):
    racy, repair = native.translate(original, task), native.translate(fixed, task)
    require(racy.shared == repair.shared and racy.locals == repair.locals, "Interfaces differ")
    globals_code = lean_list(f"⟨.{b.role},p.rows * {b.size // task.grid}⟩" for b in task.buffers)
    text = """import Lark.NativeSoftmaxWitness
open LarkNonlinear LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def sourceOriginal : List LarkCollective.Instr := [
""" + ",\n".join(collective.emit(i) for i in racy.program) + "\n]\n"
    text += "def sourceFixed : List LarkCollective.Instr := [\n" + ",\n".join(collective.emit(i) for i in repair.program) + f"""
]
def sourceShared : List Nat := {[n for _, n in racy.shared]}
def sourceLocals : List Nat := {[n for _, n in racy.locals]}
def sourceLayout (p : Shape) : Layout := ⟨{globals_code},sourceShared,sourceLocals⟩
def sourceGeometry (p : Shape) : Geometry := ⟨p.rows,{task.block},{task.warp}⟩
def sourceFuel : Fuel := ⟨{','.join(map(str,task.fuel))}⟩
theorem source_program_data : sourceOriginal = racyProgram ∧ sourceFixed = fixedProgram := by decide
theorem source_interface_data (p : Shape) :
    sourceLayout p = layout p ∧ sourceGeometry p = geometry p ∧ sourceFuel = fuel := ⟨rfl,rfl,rfl⟩
def sourceStep (p : Shape) (guarded : Bool) (ops : Ops α) (t : Nat) (s : State α) : Option (State α) := do
  match ← (if guarded then sourceFixed else sourceOriginal)[s.pc t]? with
  | .scalar i => execute ops (sourceLayout p) (sourceGeometry p) t i s
  | .shuffle .. => none
theorem source_step_data (p : Shape) (guarded : Bool) (ops : Ops α) (t : Nat) (s : State α) :
    sourceStep p guarded ops t s = sourceScalarStep p guarded ops t s := by
  simp only [sourceStep,sourceScalarStep,program,source_program_data.1,source_program_data.2,
    (source_interface_data p).1,(source_interface_data p).2.1]
  cases h : (if guarded then fixedProgram else racyProgram)[s.pc t]? with
  | none => rfl
  | some i => cases i <;> rfl
theorem source_reader_trace (p : Shape) (ops : Ops α) (x : α) :
    (sourceStep p false ops 0 (readerStart 50256 2 x)).map State.trace =
      some [⟨0,⟨.local,0,1,2⟩,true,⟨0,4,0⟩⟩,reader] := by
  rewrite [source_step_data]
  exact reader_step p ops x
theorem source_writer_trace (p : Shape) (ops : Ops α) (x denominator : α) :
    (sourceStep p false ops 80 (writerStart 50256 x denominator)).map State.trace = some [writerAccess] := by
  rewrite [source_step_data]
  exact writer_step p ops x denominator
theorem source_guard_trace (p : Shape) :
    (sourceStep p true unitOps 0 guardStart).map (fun s => (s.pc 0,s.trace)) = some (102,[]) := by
  rewrite [source_step_data]
  exact guard_step p
theorem source_pair_conflicts (p : Shape) : conflict (sourceGeometry p) reader writerAccess = true := by
  rewrite [(source_interface_data p).2.1]
  exact pair_conflict p
theorem source_sufficient_rf (p : Shape) (trace : List Access) (h : ∀ a ∈ trace, Good a) :
    raceFree (sourceGeometry p) trace = true := by
  rewrite [(source_interface_data p).2.1]
  exact race_free p trace h
#print axioms source_program_data
#print axioms source_interface_data
#print axioms source_step_data
#print axioms source_reader_trace
#print axioms source_writer_trace
#print axioms source_guard_trace
#print axioms source_pair_conflicts
#print axioms source_sufficient_rf
"""
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    original = (HERE / "cases/native_race/kernel.hip").read_text()
    fixed = (HERE / "cases/native_fixed/kernel.hip").read_text()
    require(original == expected_source(False) and fixed == expected_source(True), "Generated adaptation differs")
    task = native.parse_task((HERE / "cases/native_race/task.json").read_text())
    require(native.parse_task((HERE / "cases/native_fixed/task.json").read_text()).buffers == task.buffers,
            "Repair changed tensor interface")
    closure = set()
    modules(TARGET, closure)
    for module in sorted(closure):
        path = module.replace(".", "/") + ".lean"
        dest = project / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean" / path, dest)
    (project / "lakefile.toml").write_text('''name = "native_softmax_components"
version = "0.1.0"
defaultTargets = ["Main"]
[[lean_lib]]
name = "Lark"
[[lean_lib]]
name = "Main"
''')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    (project / "reproduction/__init__.py").write_bytes((ROOT / "reproduction/__init__.py").read_bytes())
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    (project / "validate_source.py").write_text('''from pathlib import Path
from lark_kernels import native_softmax as native
from reproduction.production_softmax.check_program import statement, HERE
from reproduction.production_softmax.prepare import source
root = Path(__file__).resolve().parent
original = (HERE / "cases/native_race/kernel.hip").read_text()
fixed = (HERE / "cases/native_fixed/kernel.hip").read_text()
assert original == source(False) and fixed == source(True)
task = native.parse_task((HERE / "cases/native_race/task.json").read_text())
assert (root / "Main.lean").read_text() == statement(original,fixed,task)
print("Frozen reader, exact readback and both complete source-to-Main program/interface bindings passed.")
''')
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    checks = []

    def execute(name, command, expected):
        before = time.monotonic()
        result = subprocess.run(command, cwd=project, capture_output=True, text=True, timeout=180)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        accepted = result.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("is false" in log and "error:" in log and "maximum" not in log,
                    "Wrong negative gate: " + name)
        checks.append({"name": name, "expected_accepted": expected, "accepted": accepted,
                       "exit_code": result.returncode, "seconds": time.monotonic() - before, "timed_out": False})
        return log

    execute("frozen-reader", [sys.executable, "validate_source.py"], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require({"source_program_data", "source_reader_trace", "source_writer_trace", "source_guard_trace",
             "LarkNativeSoftmax.reader_step", "LarkNativeSoftmax.pair_conflict", "LarkNativeSoftmax.race_free"} <= audits.keys(),
            "Principal audits absent")
    for name, axioms in audits.items():
        require(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    controls = {
        "wrong-max-reduction": statement(original.replace("__shfl_down(maxval, 16, 32)",
                                                          "__shfl_xor(maxval, 16, 32)", 1), fixed, task),
        "wrong-clamped-cell": statement(original.replace("norm_load_col = 50256", "norm_load_col = 50255", 1), fixed, task),
        "missing-first-barrier": statement(original.replace("__syncthreads();", "", 1), fixed, task),
        "wrong-normalization-value": statement(original.replace("norm_value / total_sum", "norm_value", 1), fixed, task),
        "wrong-private-layout": positive.replace("def sourceLocals : List Nat := [8, 8]", "def sourceLocals : List Nat := [8, 7]", 1) + "\nexample : sourceLocals = [8,8] := by decide\n",
        "wrong-block-fuel": positive.replace("def sourceFuel : Fuel := ⟨4096,8,5,1⟩", "def sourceFuel : Fuel := ⟨4096,8,4,1⟩", 1) + "\nexample : sourceFuel = LarkNativeSoftmax.fuel := by decide\n",
        "false-original-race-freedom": """import Main
open LarkNativeSoftmax LarkNonlinear
example : raceFree (sourceGeometry ⟨1, by decide, by decide⟩) [reader,writerAccess] = true := by decide
""",
        "wrong-writer-address": """import Main
open LarkNativeSoftmax LarkNonlinear
def wrongWriter : Access := ⟨79,globalCell 0 (column 79 6 1),true,⟨0,4,0⟩⟩
example : conflict (sourceGeometry ⟨1, by decide, by decide⟩) reader wrongWriter = true := by decide
""",
        "false-repair-takes-load": """import Main
open LarkNativeSoftmax LarkNonlinear
example : (sourceStep ⟨1, by decide, by decide⟩ true unitOps 0 guardStart).map
    (fun s => (s.pc 0,s.trace)) = some (100,[]) := by
  rewrite [source_guard_trace]
  decide
""",
    }
    for name, text in controls.items():
        require(text != positive, "Vacuous mutation: " + name)
        (project / (name + ".lean")).write_text(text)
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    (project / "README.md").write_text(
        "Check source/reader binding: python3 validate_source.py. Fresh proof: lake build.\n"
        "The nine other root Lean files intentionally fail.\n"
        "Full source identity, loop-address coverage, conditional footprint RF and single-instruction trace witness only.\n"
        "The witness states are explicit intermediates; full initializer reachability/reference equivalence remains open.\n"
        "No source certificate or original-paper completion is claimed.\n")
    files = sorted(p for p in project.rglob("*") if p.is_file() and ".lake" not in p.relative_to(project).parts
                   and "__pycache__" not in p.relative_to(project).parts)
    (out / "source-manifest.json").write_text(json.dumps({str(p.relative_to(project)): sha(p) for p in files}, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for path in files:
            info = archive.gettarinfo(str(path), arcname=str(path.relative_to(project)))
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ""
            with path.open("rb") as stream:
                archive.addfile(info, stream)
    shutil.copyfile(Path(__file__), out / "checker.py")
    report = {
        "schema": 1, "status": "native-softmax-source-and-instruction-witness-checked",
        "local_lean_modules": len(closure), "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(controls), "checks": checks,
        "source_certificates": 0, "full_source_identity_checked": True,
        "instruction_trace_counterexample_proved": True, "repaired_guard_step_proved": True,
        "sufficient_footprint_race_freedom_proved": True, "whole_kernel_execution_proved": False,
        "intermediate_state_reachability_proved": False, "actual_trace_universal_classification_proved": False,
        "canonical_source_equivalence_proved": False, "ieee_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(closure), "audits": len(audits), "rejections": len(controls)}))


if __name__ == "__main__":
    main()
