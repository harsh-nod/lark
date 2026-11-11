"""Fresh source-bound native softmax maximum block phase and barrier resume.

The first scheduler wave-fold completes and the first block barrier resumes.
The resulting decomposition leaves the remaining four block phases explicit;
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
from reproduction.production_softmax import check_first_wave as wave  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

base, prefix, native = wave.base, wave.prefix, wave.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxMaxBarrier"
sha, require = wave.sha, wave.require


def golden_checksum(logical):
    warp, half = divmod(logical, 2)
    values = []
    for lane in range(64):
        accumulator = 0
        tid = warp * 64 + lane
        for iteration in range(7):
            for component in range(8):
                column = min(50256, tid + iteration * 8192 + component * 1024)
                accumulator = 3 * accumulator + column + 1
        values.append(accumulator)
    for distance in (16, 8, 4, 2, 1):
        values = [3 * value + values[lane + distance if lane % 32 + distance < 32 else lane]
                  for lane, value in enumerate(values)]
    return values[half * 32]


def statement(original, fixed, task):
    text = wave.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxMaxWaveTree\n",
        "import Lark.NativeSoftmaxMaxWaveTree\nimport Lark.NativeSoftmaxMaxBarrier\n", 1)
    text += '''
def sourceBlockFold (p : Shape) (guarded : Bool) (ops : Ops α) (row : Nat) (s : State α) : Option (State α) :=
  (List.range (((sourceGeometry p).block+(sourceGeometry p).warp-1)/(sourceGeometry p).warp)).foldlM
    (fun s w => sourceWarp p guarded ops (warpThreads (sourceGeometry p) row w) sourceFuel.warp s) s
def sourceBlock (p : Shape) (guarded : Bool) (ops : Ops α) (row budget : Nat) (s : State α) : Option (State α) :=
  LarkPartitionCollective.runBlock ops (sourceLayout p) (sourceGeometry p) sourceFuel
    (if guarded then sourceFixed else sourceOriginal) row budget s
def sourceBlockState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) : State α :=
  firstBlock p ops input row (sourceInitial p input outside)
def sourceMidState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) : State α :=
  midState p ops input row (sourceInitial p input outside)
theorem source_block_fold_data (p : Shape) (guarded : Bool) (ops : Ops α) (row : Nat) (s : State α) :
    sourceBlockFold p guarded ops row s =
      (List.range 16).foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel
        (program guarded) (warpThreads (geometry p) row w) fuel.warp s) s := by
  simp only [sourceBlockFold,source_warp_data,(source_interface_data p).2.1,(source_interface_data p).2.2]
  have hcount : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp = 16 := by
    change (1024+64-1)/64 = 16
    decide
  rewrite [hcount]
  rfl
theorem source_block_data (p : Shape) (guarded : Bool) (ops : Ops α) (row budget : Nat) (s : State α) :
    sourceBlock p guarded ops row budget s =
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row budget s := by
  simp only [sourceBlock,program,source_program_data.1,source_program_data.2,
    (source_interface_data p).1,(source_interface_data p).2.1,(source_interface_data p).2.2]
theorem source_block_initial_fold_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    sourceBlockFold p guarded ops row (sourceInitial p input outside) =
      some (sourceBlockState p ops input outside row) := by
  rewrite [source_block_fold_data,source_initial_data]
  exact first_block_initial_run p guarded ops input outside row hr
theorem source_block_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    (sourceBlockState p ops input outside row).pc (row*1024+tid) = 32 :=
  (first_block_member p ops input row tid _ (initial_block_entry p input outside row hr) ht).pc
theorem source_block_initial_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row logicalWarp : Nat) (hw : logicalWarp < 32) :
    (sourceBlockState p ops input outside row).memory ⟨.shared,row,0,logicalWarp⟩ =
      some (blockPartial ops input row logicalWarp) :=
  first_block_partial p ops input row logicalWarp _ hw
theorem source_block_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    ∀ a ∈ (sourceBlockState p ops input outside row).trace, Good a :=
  first_block_good p ops input row _ (initial_block_entry p input outside row hr)
theorem source_block_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (sourceGeometry p) (sourceBlockState p ops input outside row).trace = true := by
  rewrite [(source_interface_data p).2.1]
  exact first_block_initial_race_free p ops input outside row hr
theorem source_trace_length_of_nil (start final : State α) (n : Nat) (hempty : start.trace = [])
    (h : final.trace.length = start.trace.length+n) : final.trace.length = n := by
  rewrite [hempty] at h
  simpa only [List.length_nil,Nat.zero_add] using h
theorem source_block_initial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (firstBlock p ops input row (sourceInitial p input outside)).trace.length = 57376 :=
  source_trace_length_of_nil (sourceInitial p input outside)
    (firstBlock p ops input row (sourceInitial p input outside)) 57376 rfl
    (first_block_trace_length p ops input row (sourceInitial p input outside))
theorem source_block_initial_partial_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row logicalWarp : Nat)
    (hr : row < p.rows) (hw : logicalWarp < 32) :
    (sourceBlockFold p guarded ops row (sourceInitial p input outside)).map
      (fun s => s.memory ⟨.shared,row,0,logicalWarp⟩) = some (some (blockPartial ops input row logicalWarp)) :=
  source_memory_of_run _ _ _ _ (source_block_initial_fold_run p guarded ops input outside row hr)
    (source_block_initial_partial p ops input outside row logicalWarp hw)
theorem source_mid_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    (sourceMidState p ops input outside row).pc (row*1024+tid) = 33 :=
  (initial_mid_ready p ops input outside row hr).pc tid ht
theorem source_mid_initial_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    ((sourceMidState p ops input outside row).epochs (row*1024+tid)).block = 1 :=
  (initial_mid_ready p ops input outside row hr).epoch tid ht
theorem source_mid_initial_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (l : Location) (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (sourceMidState p ops input outside row).memory l = (sourceInitial p input outside).memory l :=
  mid_memory_frame p ops input row _ l hl
theorem source_mid_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (sourceGeometry p) (sourceMidState p ops input outside row).trace = true := by
  rewrite [(source_interface_data p).2.1]
  exact initial_mid_race_free p ops input outside row hr
theorem source_initial_block_barrier (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    sourceBlock p guarded ops row sourceFuel.block (sourceInitial p input outside) =
      sourceBlock p guarded ops row 4 (sourceMidState p ops input outside row) := by
  rewrite [source_block_data,source_block_data,(source_interface_data p).2.2,source_initial_data]
  exact initial_first_barrier p guarded ops input outside row hr
def checksumOps : Ops Nat where
  literal := fun _ _ => 0
  add := Nat.add
  sub := Nat.sub
  mul := Nat.mul
  max := fun a b => 3*a+b
  div := Nat.div
  exp := id
  tanh := id
  rsqrt := id
  fromHalf := id
  toHalf := id
def checksumInput : Nat → Nat → Nat := fun _ offset => offset+1
'''
    value = golden_checksum(31)
    text += f'''theorem source_checksum_last_partial : blockPartial checksumOps checksumInput 0 31 = {value} := by decide
theorem source_checksum_last_partial_run (guarded : Bool) :
    (sourceBlockFold prefixOne guarded checksumOps 0 (sourceInitial prefixOne checksumInput (fun _ => none))).map
      (fun s => s.memory ⟨.shared,0,0,31⟩) = some (some {value}) := by
  exact (source_block_initial_partial_run prefixOne guarded checksumOps checksumInput (fun _ => none) 0 31
    (by decide) (by decide)).trans (congrArg (fun v : Nat => some (some v)) source_checksum_last_partial)
'''
    for name in ("source_block_fold_data", "source_block_data", "source_block_initial_fold_run",
                 "source_block_initial_pc", "source_block_initial_partial", "source_block_initial_good",
                 "source_block_initial_rf", "source_trace_length_of_nil", "source_block_initial_trace_length", "source_block_initial_partial_run",
                 "source_mid_initial_pc", "source_mid_initial_epoch", "source_mid_initial_memory_frame",
                 "source_mid_initial_rf", "source_initial_block_barrier", "source_checksum_last_partial",
                 "source_checksum_last_partial_run"):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    result = wave.controls(original, fixed, task, positive)
    common = "import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-block-endpoint"] = common + '''example :
    (sourceBlockState prefixOne wordOps wordInput (fun _ => none) 0).pc (0*1024+0) = 31 := by
  rewrite [source_block_initial_pc prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-block-trace-length"] = common + '''example :
    (firstBlock prefixOne wordOps wordInput 0 (sourceInitial prefixOne wordInput (fun _ => none))).trace.length = 57344 := by
  rewrite [source_block_initial_trace_length]
  decide
'''
    result["wrong-resumed-pc"] = common + '''example :
    (sourceMidState prefixOne wordOps wordInput (fun _ => none) 0).pc (0*1024+0) = 32 := by
  rewrite [source_mid_initial_pc prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-resumed-epoch"] = common + '''example :
    ((sourceMidState prefixOne wordOps wordInput (fun _ => none) 0).epochs (0*1024+0)).block = 0 := by
  rewrite [source_mid_initial_epoch prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-native-wave-count"] = common + "example : ((sourceGeometry prefixOne).block+(sourceGeometry prefixOne).warp-1)/(sourceGeometry prefixOne).warp = 15 := by decide\n"
    result["wrong-source-block-fuel"] = positive.replace(
        "def sourceFuel : Fuel := ⟨4096,8,5,1⟩", "def sourceFuel : Fuel := ⟨4096,8,4,1⟩", 1) + "\nexample : sourceFuel.block = 5 := by decide\n"
    wrong = golden_checksum(30)
    require(wrong != golden_checksum(31), "Vacuous last-partial checksum")
    result["wrong-final-partial-value"] = common + f"example : blockPartial checksumOps checksumInput 0 31 = {wrong} := by\n  rewrite [source_checksum_last_partial]\n  decide\n"
    result["wrong-final-partial-run-value"] = common + f'''example :
    (sourceBlockFold prefixOne true checksumOps 0 (sourceInitial prefixOne checksumInput (fun _ => none))).map
      (fun s => s.memory ⟨.shared,0,0,31⟩) = some (some {wrong}) := by
  rewrite [source_checksum_last_partial_run]
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
    (project / "lakefile.toml").write_text('name = "native_softmax_max_first_block"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_first_block import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete maximum-block and barrier-resume statement match.")
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
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require({"source_block_initial_fold_run", "source_block_initial_partial_run", "source_block_initial_good",
             "source_block_initial_rf", "source_block_initial_trace_length", "source_initial_block_barrier",
             "source_mid_initial_pc", "source_mid_initial_epoch", "source_mid_initial_rf",
             "source_checksum_last_partial", "source_checksum_last_partial_run",
             "LarkNativeSoftmax.first_block_fold_run", "LarkNativeSoftmax.first_block_partial",
             "LarkNativeSoftmax.first_block_trace_length", "LarkNativeSoftmax.mid_ready"} <= audits.keys(),
            "First-block audits absent")
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
        "Both full sources execute the actual first block wave-fold: sixteen physical waves, thirty-two partial values.\n"
        "The 57376-access trace is race-free and every lane parks at PC32 before the first barrier.\n"
        "The scheduler resumes the barrier at PC33/epoch1 with four remaining block phases explicit.\n"
        "Later serial reduction and passes, the complete launch and reference bridge remain open. Source certificates0.\n")
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
        "schema": 1, "status": "native-softmax-source-bound-maximum-first-block-checked", "stage": "max-first-block",
        "rows": {"min": 1, "max": native.MAX_ROWS}, "local_lean_modules": len(closure),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(mutations), "checks": checks,
        "actual_first_block_wave_fold_execution_proved": True, "starts_at_actual_initializer": True,
        "parked_pc": 32, "resumed_pc": 33, "block_epoch_after_resume": 1,
        "physical_waves_per_block": 16, "threads_per_block": 1024, "logical_partials_per_block": 32,
        "accesses_per_block_phase": 57376, "input_reads_per_block_phase": 57344, "shared_writes_per_block_phase": 32,
        "all32_source_ordered_partial_values_proved": True, "earlier_waves_preserved_proved": True,
        "first_barrier_resume_proved": True, "block_scheduler_decomposition_proved": True,
        "remaining_block_fuel_after_first_barrier": 4, "global_memory_frame_proved": True,
        "checksum_final_partial": golden_checksum(31), "checksum_max_operation": "3*a+b",
        "checksum_final_partial_actual_fold_value_proved": True,
        "original_fuel": {"lane":4096,"warp":8,"block":5,"grid":1},
        "first_block_race_freedom_proved": True, "race_freedom_assumed": False,
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
