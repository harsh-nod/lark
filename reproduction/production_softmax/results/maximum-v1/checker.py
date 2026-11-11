"""Fresh source-bound complete native softmax maximum pass.

Both actual block barriers resume and all 1,024 threads reach PC43/epoch2.
The remaining exponentiation/sum/normalization phases stay explicit;
no whole launch, canonical reference equivalence or source certificate is issued.
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
from reproduction.production_softmax import check_first_block as block  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

base, prefix, native = block.base, block.prefix, block.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxMaximum"
sha, require = block.sha, block.require


def golden_maximum():
    values = [block.golden_checksum(i) for i in range(32)]
    result = values[0]
    for value in values[1:]:
        result = 3 * result + value
    return result


PRINCIPAL = {
    "source_serial_initial_fold_run", "source_serial_initial_maximum_run",
    "source_maximum_initial_ready", "source_maximum_initial_pc", "source_maximum_initial_epoch",
    "source_maximum_initial_value", "source_maximum_initial_good", "source_maximum_initial_rf",
    "source_maximum_initial_trace_length", "source_maximum_initial_memory_frame",
    "source_initial_maximum_block", "source_checksum_maximum", "source_checksum_maximum_run",
    "LarkNativeSoftmax.serial_block_fold_run", "LarkNativeSoftmax.serial_block_step",
    "LarkNativeSoftmax.initial_maximum_ready", "LarkNativeSoftmax.initial_maximum_block",
    "LarkNativeSoftmax.maximum_trace_length", "LarkNativeSoftmax.initial_maximum_race_free",
    "source_block_initial_fold_run", "source_checksum_last_partial_run", "source_initial_block_barrier",
}


def statement(original, fixed, task):
    text = block.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxMaxBarrier\n",
        "import Lark.NativeSoftmaxMaxBarrier\nimport Lark.NativeSoftmaxMaximum\n", 1)
    text += '''
def sourceMaximumState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) : State α :=
  maximumState p ops input row (sourceInitial p input outside)
theorem source_serial_initial_fold_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    sourceBlockFold p guarded ops row (sourceMidState p ops input outside row) =
      some (serialBlock ops input row (sourceMidState p ops input outside row)) := by
  rewrite [source_block_fold_data]
  have h := serial_block_fold_run p guarded ops input row (sourceMidState p ops input outside row)
    (initial_mid_ready p ops input outside row hr)
  have hcount : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rewrite [hcount] at h
  exact h
theorem source_serial_initial_maximum_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    (sourceBlockFold p guarded ops row (sourceMidState p ops input outside row)).map
      (fun s => s.memory ⟨.shared,row,0,0⟩) = some (some (rowMaximum ops input row)) :=
  source_memory_of_run _ _ _ _ (source_serial_initial_fold_run p guarded ops input outside row hr)
    (serial_block_value ops input row _)
theorem source_maximum_initial_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    MaximumReady p ops input row (sourceMaximumState p ops input outside row) :=
  initial_maximum_ready p ops input outside row hr
theorem source_maximum_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    (sourceMaximumState p ops input outside row).pc (row*1024+tid)=43 :=
  (source_maximum_initial_ready p ops input outside row hr).pc tid ht
theorem source_maximum_initial_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceMaximumState p ops input outside row).epochs (row*1024+tid)).block=2 :=
  (source_maximum_initial_ready p ops input outside row hr).epoch tid ht
theorem source_maximum_initial_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    (sourceMaximumState p ops input outside row).memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row) :=
  (source_maximum_initial_ready p ops input outside row hr).maximum
theorem source_maximum_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    ∀ a ∈ (sourceMaximumState p ops input outside row).trace, Good a :=
  (source_maximum_initial_ready p ops input outside row hr).good
theorem source_maximum_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    raceFree (sourceGeometry p) (sourceMaximumState p ops input outside row).trace=true := by
  rewrite [(source_interface_data p).2.1]
  exact initial_maximum_race_free p ops input outside row hr
theorem source_maximum_initial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (maximumState p ops input row (sourceInitial p input outside)).trace.length=57409 :=
  source_trace_length_of_nil (sourceInitial p input outside)
    (maximumState p ops input row (sourceInitial p input outside)) 57409 rfl
    (maximum_trace_length p ops input row (sourceInitial p input outside))
theorem source_maximum_initial_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (l : Location) (hl : l.space=.global ∨ l.buffer ≠ 0) :
    (sourceMaximumState p ops input outside row).memory l=(sourceInitial p input outside).memory l :=
  maximum_memory_frame p ops input row _ l hl
theorem source_initial_maximum_block (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    sourceBlock p guarded ops row sourceFuel.block (sourceInitial p input outside) =
      sourceBlock p guarded ops row 3 (sourceMaximumState p ops input outside row) := by
  rewrite [source_block_data,source_block_data,(source_interface_data p).2.2,source_initial_data]
  exact initial_maximum_block p guarded ops input outside row hr
'''
    partial_names = []
    for i in range(31):
        name = "source_checksum_partial_" + str(i)
        text += f"theorem {name} : blockPartial checksumOps checksumInput 0 {i} = {block.golden_checksum(i)} := by decide\n"
        partial_names.append(name)
    partial_names.append("source_checksum_last_partial")
    text += f'''theorem source_checksum_maximum : rowMaximum checksumOps checksumInput 0 = {golden_maximum()} := by
  simp only [rowMaximum,serialMaximum,serialFold,{", ".join(partial_names)}]
  decide
theorem source_checksum_maximum_run (guarded : Bool) :
    (sourceBlockFold prefixOne guarded checksumOps 0 (sourceMidState prefixOne checksumOps checksumInput (fun _ => none) 0)).map
      (fun s => s.memory ⟨.shared,0,0,0⟩) = some (some {golden_maximum()}) := by
  exact (source_serial_initial_maximum_run prefixOne guarded checksumOps checksumInput (fun _ => none) 0
    (by decide)).trans (congrArg (fun v : Nat => some (some v)) source_checksum_maximum)
'''
    for name in sorted(PRINCIPAL | set(partial_names)):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    # Earlier source/IR controls retain their independent, smaller statements.
    # Every claim about this new endpoint imports the current complete Main.
    result = block.controls(original, fixed, task, block.statement(original, fixed, task))
    for name, before, after in (
        ("changed-serial-leader", "if (tid == 0)", "if (tid == 1)"),
        ("changed-serial-bound", "while (max_warp < 32)", "while (max_warp < 31)"),
        ("changed-serial-start", "int max_warp = 1", "int max_warp = 2"),
        ("swapped-serial-operands", "fmaxf(block_max, warp_max)", "fmaxf(warp_max, block_max)"),
        ("changed-serial-store", "maxvals[0] = block_max", "maxvals[1] = block_max"),
        ("omitted-second-block-barrier", "maxvals[0] = block_max;\n}\n__syncthreads();", "maxvals[0] = block_max;\n}"),
    ):
        changed = original.replace(before, after, 1)
        require(changed != original, "Vacuous serial source control: " + name)
        result[name] = block.statement(changed, fixed, task)
    common = "import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-maximum-endpoint"] = common + '''example :
    (sourceMaximumState prefixOne wordOps wordInput (fun _ => none) 0).pc (0*1024+0)=42 := by
  rewrite [source_maximum_initial_pc prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-maximum-epoch"] = common + '''example :
    ((sourceMaximumState prefixOne wordOps wordInput (fun _ => none) 0).epochs (0*1024+0)).block=1 := by
  rewrite [source_maximum_initial_epoch prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-maximum-trace-length"] = common + '''example :
    (maximumState prefixOne wordOps wordInput 0 (sourceInitial prefixOne wordInput (fun _ => none))).trace.length=57376 := by
  rewrite [source_maximum_initial_trace_length]
  decide
'''
    wrong = block.golden_checksum(31)
    require(wrong != golden_maximum(), "Vacuous maximum checksum")
    result["wrong-row-maximum-value"] = common + f"example : rowMaximum checksumOps checksumInput 0 = {wrong} := by\n  rewrite [source_checksum_maximum]\n  decide\n"
    result["wrong-row-maximum-run-value"] = common + f'''example :
    (sourceBlockFold prefixOne true checksumOps 0 (sourceMidState prefixOne checksumOps checksumInput (fun _ => none) 0)).map
      (fun s => s.memory ⟨.shared,0,0,0⟩) = some (some {wrong}) := by
  rewrite [source_checksum_maximum_run]
  decide
'''
    return result


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
    require(original == source(False) and fixed == source(True), "Generated source differs")
    task = native.parse_task((HERE / "cases/native_race/task.json").read_text())
    closure = set()
    base.modules(TARGET, closure)
    base.modules(base.TARGET, closure)
    base.modules(prefix.TARGET, closure)
    for module in sorted(closure):
        path = module.replace(".", "/") + ".lean"
        destination = project / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean" / path, destination)
    (project / "lakefile.toml").write_text('name = "native_softmax_maximum"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_maximum import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete maximum-pass and both-barrier statement match.")
''')
    checks = []

    def execute(name, command, expected):
        before = time.monotonic()
        run = subprocess.run(command, cwd=project, capture_output=True, text=True, timeout=180)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("is false" in log and "maximum recursion depth" not in log
                    and "maximum heartbeats" not in log and "deep recursion detected" not in log,
                    "Wrong rejection gate: " + name)
        checks.append({"name": name, "expected_accepted": expected, "accepted": accepted,
                       "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
        return log

    execute("frozen-reader", [sys.executable, "validate_source.py"], True)
    execute("fresh-library-build", ["lake", "build", TARGET, base.TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Maximum-pass audits absent")
    for name, axioms in audits.items():
        require(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    mutations = controls(original, fixed, task, positive)
    for name, text in mutations.items():
        require(text != positive, "Vacuous control: " + name)
        (project / (name + ".lean")).write_text(text)
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    (project / "README.md").write_text(
        "Fresh checks: python3 validate_source.py; lake build. All other root Lean files intentionally fail.\n"
        "Both full sources execute the actual maximum pass, with all32 source-ordered partials reduced by thread0.\n"
        "All1024 participating threads resume both block barriers and reach PC43/epoch2.\n"
        "The57409-access trace is race-free; the original scheduler retains three remaining block phases.\n"
        "Later exponentiation/sum/normalization, whole launch and reference bridge remain open. Source certificates0.\n")
    files = sorted(p for p in project.rglob("*") if p.is_file()
                   and not {".lake", "__pycache__"}.intersection(p.relative_to(project).parts))
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
        "schema": 1, "status": "native-softmax-source-bound-maximum-pass-checked", "stage": "maximum-pass",
        "rows": {"min": 1, "max": native.MAX_ROWS}, "local_lean_modules": len(closure),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(mutations), "checks": checks,
        "actual_first_block_wave_fold_execution_proved": True, "starts_at_actual_initializer": True,
        "parked_pc": 42, "resumed_pc": 43, "block_epoch_after_resume": 2,
        "physical_waves_per_block": 16, "threads_per_block": 1024, "logical_partials_per_block": 32,
        "accesses_per_maximum_pass": 57409, "input_reads_per_maximum_pass": 57344, "shared_writes_per_maximum_pass": 33, "shared_reads_per_maximum_pass": 32,
        "all32_source_ordered_partial_values_proved": True, "earlier_waves_preserved_proved": True,
        "first_barrier_resume_proved": True, "block_scheduler_decomposition_proved": True,
        "remaining_block_fuel_after_maximum": 3, "global_memory_frame_proved": True,
        "checksum_final_partial": block.golden_checksum(31), "checksum_row_maximum": golden_maximum(), "checksum_max_operation": "3*a+b",
        "checksum_final_partial_actual_fold_value_proved": True,
        "original_fuel": {"lane":4096,"warp":8,"block":5,"grid":1},
        "first_block_race_freedom_proved": True, "race_freedom_assumed": False,
        "actual_serial_block_wave_fold_execution_proved": True, "all32_serial_partial_reads_proved": True,
        "second_barrier_resume_proved": True, "maximum_pass_race_freedom_proved": True,
        "checksum_row_maximum_actual_fold_value_proved": True,
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "conflict_witness_state_reachability_proved": False, "actual_trace_universal_classification_proved": False,
        "canonical_source_equivalence_proved": False, "ieee_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(closure), "audits": len(audits), "rejections": len(mutations)}))


if __name__ == "__main__":
    main()
