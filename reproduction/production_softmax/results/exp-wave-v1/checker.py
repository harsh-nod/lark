"""Fresh source-bound native softmax scalar exponentiation/sum prefix.

After the proved maximum pass, each native64 wave executes all seven scalar
rounds and five logical32 XOR/add stages, then parks at PC82. Later phases stay open;
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
from reproduction.production_softmax import check_exp_prefix as lane  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

maximum = lane.maximum
base, prefix, native = lane.base, lane.prefix, lane.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxExpWave"
sha, require = maximum.sha, maximum.require


WORD_TIDS, WORD_MAXIMUM, WORD_MODEL = lane.WORD_TIDS, lane.WORD_MAXIMUM, lane.WORD_MODEL
golden_word = lane.golden_word
WAVE_CASES = ((0,0),(0,1),(1,0),(1,1),(15,0),(15,1))


def golden_wave(warp, *, reverse_add=False, sequential=False, cross_half=False):
    values = [golden_word(warp*64+i)["sum"] for i in range(64)]
    for mask in (16,8,4,2,1):
        old = values if sequential else values.copy()
        order = range(63,-1,-1) if sequential else range(64)
        for i in order:
            peer = (i%32)^mask if cross_half else (i//32)*32+((i%32)^mask)
            a,b = old[i],old[peer]
            values[i] = 7*b+a if reverse_add else 7*a+b
    return values


WAVE_PRINCIPAL = {
    "source_exp_wave_initial_run", "source_exp_wave_initial_pc", "source_exp_wave_initial_epoch",
    "source_exp_wave_initial_partial", "source_exp_wave_partial_run", "source_exp_wave_initial_good",
    "source_exp_wave_initial_rf", "source_exp_wave_initial_sum", "source_exp_wave_sum_run",
    "LarkNativeSoftmax.exp_wave_run", "LarkNativeSoftmax.exp_wave_of_maximum",
    "LarkNativeSoftmax.initial_exp_wave", "LarkNativeSoftmax.exp_wave_sum",
    "LarkNativeSoftmax.exp_wave_partial", "LarkNativeSoftmax.exp_wave_race_free",
    "LarkNativeSoftmax.cohort_sum_xor_shuffle", "LarkNativeSoftmax.sum_xor_peer_partition",
    "LarkNativeSoftmax.native_sum_first_four_of_cohort", "LarkNativeSoftmax.sum_last_wave_warp",
}
PRINCIPAL = lane.PRINCIPAL | WAVE_PRINCIPAL


def statement(original, fixed, task):
    text = lane.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxExpPrefixCounts\n",
        "import Lark.NativeSoftmaxExpPrefixCounts\nimport Lark.NativeSoftmaxExpWave\n", 1)
    text += r"""
def sourceExpWaveState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) : State α :=
  expWave p ops input row warp (sourceMaximumState p ops input outside row)
theorem source_exp_wave_initial_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<p.rows) (hw : warp<16) :
    sourceWarp p guarded ops (warpThreads (sourceGeometry p) row warp) sourceFuel.warp
      (sourceMaximumState p ops input outside row)=some (sourceExpWaveState p ops input outside row warp) := by
  rewrite [source_warp_data,(source_interface_data p).2.1,(source_interface_data p).2.2]
  exact exp_wave_of_maximum p guarded ops input row warp _ hw (source_maximum_initial_ready p ops input outside row hr)
theorem source_exp_wave_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hl : lane<64) :
    (sourceExpWaveState p ops input outside row warp).pc (cohortBase row warp+lane)=82 :=
  exp_wave_pc p ops input row warp lane _ hl
theorem source_exp_wave_initial_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hr : row<p.rows) (hw : warp<16) (hl : lane<64) :
    ((sourceExpWaveState p ops input outside row warp).epochs (cohortBase row warp+lane)).block=2 := by
  have h := congrArg (fun epochs => (epochs (cohortBase row warp+lane)).block)
    (exp_wave_epochs p ops input row warp (sourceMaximumState p ops input outside row))
  apply h.trans
  simpa only [cohortBase,Nat.add_assoc] using
    source_maximum_initial_epoch p ops input outside row (warp*64+lane) hr (by omega)
theorem source_exp_wave_initial_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp half : Nat) (hw : warp<16) (hh : half<2) :
    (sourceExpWaveState p ops input outside row warp).memory ⟨.shared,row,1,warp*2+half⟩=
      some (sumWaveValues ops input row warp 5 (half*32)) :=
  exp_wave_partial p ops input row warp half _ hw hh
theorem source_exp_wave_partial_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp half : Nat) (hr : row<p.rows) (hw : warp<16) (hh : half<2) :
    (sourceWarp p guarded ops (warpThreads (sourceGeometry p) row warp) sourceFuel.warp
      (sourceMaximumState p ops input outside row)).map (fun s => s.memory ⟨.shared,row,1,warp*2+half⟩)=
        some (some (sumWaveValues ops input row warp 5 (half*32))) :=
  source_memory_of_run _ (sourceExpWaveState p ops input outside row warp) _ _
    (source_exp_wave_initial_run p guarded ops input outside row warp hr hw)
    (source_exp_wave_initial_partial p ops input outside row warp half hw hh)
theorem source_exp_wave_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<p.rows) (hw : warp<16) :
    ∀ a ∈ (sourceExpWaveState p ops input outside row warp).trace, Good a :=
  exp_wave_good p ops input row warp _ hw (exp_cohort_entry_of_maximum p ops input row warp _ hw
    (source_maximum_initial_ready p ops input outside row hr))
theorem source_exp_wave_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<p.rows) (hw : warp<16) :
    raceFree (sourceGeometry p) (sourceExpWaveState p ops input outside row warp).trace=true := by
  rewrite [(source_interface_data p).2.1]
  exact race_free p _ (source_exp_wave_initial_good p ops input outside row warp hr hw)
theorem source_exp_wave_initial_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hw : warp<16) (hl : lane<64) :
    (sourceExpWaveState p ops input outside row warp).regs (cohortBase row warp+lane) 6=
      some (sumWaveValues ops input row warp 5 lane) :=
  exp_wave_sum p ops input row warp lane _ hw hl
theorem source_exp_wave_sum_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hr : row<p.rows) (hw : warp<16) (hl : lane<64) :
    (sourceWarp p guarded ops (warpThreads (sourceGeometry p) row warp) sourceFuel.warp
      (sourceMaximumState p ops input outside row)).map (fun s => s.regs (cohortBase row warp+lane) 6)=
        some (some (sumWaveValues ops input row warp 5 lane)) :=
  source_exp_register_of_run _ (sourceExpWaveState p ops input outside row warp) _ _ _
    (source_exp_wave_initial_run p guarded ops input outside row warp hr hw)
    (source_exp_wave_initial_sum p ops input outside row warp lane hw hl)
"""
    names = set(WAVE_PRINCIPAL)
    for warp,half in WAVE_CASES:
        value = golden_wave(warp)[half*32]
        name = f"exp_wave_word_{warp}_{half}"
        actual = f"source_exp_wave_word_{warp}_{half}"
        text += f"""theorem {name} : sumWaveValues expWordOps expWordInput 0 {warp} 5 ({half}*32)={value} := by
  simp only [sumWaveValues,threadExpSum,exp_word_maximum]
  decide
theorem {actual} (guarded : Bool) :
    (sourceWarp expWordOne guarded expWordOps (warpThreads (sourceGeometry expWordOne) 0 {warp}) sourceFuel.warp
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.memory ⟨.shared,0,1,{warp}*2+{half}⟩)=some (some {value}) :=
  (source_exp_wave_partial_run expWordOne guarded expWordOps expWordInput (fun _ => none) 0 {warp} {half}
    (by decide) (by decide) (by decide)).trans (congrArg (fun n : Nat => some (some n)) {name})
"""
        names |= {name,actual}
    for name in sorted(names):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    result = lane.controls(original,fixed,task,lane.statement(original,fixed,task))
    for name,before,after in (
        ("changed-sum-xor-kind","__shfl_xor(sumval, 16, 32)","__shfl_down(sumval, 16, 32)"),
        ("changed-sum-last-distance","__shfl_xor(sumval, 1, 32)","__shfl_xor(sumval, 2, 32)"),
        ("changed-sum-logical-width","__shfl_xor(sumval, 16, 32)","__shfl_xor(sumval, 16, 64)"),
        ("changed-sum-source-register","__shfl_xor(sumval, 16, 32)","__shfl_xor(sum_other, 16, 32)"),
        ("swapped-sum-operands","sumval = sumval + sum_other;","sumval = sum_other + sumval;"),
        ("changed-sum-partial-bank","sumvals[warp_id] = sumval;","maxvals[warp_id] = sumval;"),
        ("changed-sum-partial-slot","sumvals[warp_id] = sumval;","sumvals[0] = sumval;"),
        ("changed-sum-partial-leader","if (lane_id == 0) { sumvals","if (lane_id == 1) { sumvals"),
        ("omitted-third-block-barrier","sumvals[warp_id] = sumval; }\n__syncthreads();","sumvals[warp_id] = sumval; }"),
    ):
        changed=original.replace(before,after,1)
        require(changed!=original,"Vacuous sum source control: "+name)
        result[name]=maximum.block.statement(changed,fixed,task)
    common="import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-exp-wave-endpoint"]=common+"""example :
    (sourceExpWaveState expWordOne expWordOps expWordInput (fun _ => none) 0 0).pc (cohortBase 0 0+0)=83 := by
  rewrite [source_exp_wave_initial_pc expWordOne expWordOps expWordInput (fun _ => none) 0 0 0 (by decide)]
  decide
"""
    result["invented-third-barrier-resume"]=common+"""example :
    ((sourceExpWaveState expWordOne expWordOps expWordInput (fun _ => none) 0 0).epochs (cohortBase 0 0+0)).block=3 := by
  rewrite [source_exp_wave_initial_epoch expWordOne expWordOps expWordInput (fun _ => none) 0 0 0
    (by decide) (by decide) (by decide)]
  decide
"""
    result["invented-exp-wave-none"]=common+"""example :
    (sourceWarp expWordOne false expWordOps (warpThreads (sourceGeometry expWordOne) 0 0) sourceFuel.warp
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).isSome=false := by
  rewrite [source_exp_wave_initial_run expWordOne false expWordOps expWordInput (fun _ => none) 0 0 (by decide) (by decide)]
  change true=false
  decide
"""
    cases = (("reversed-sum-tree-value",0,0,golden_wave(0,reverse_add=True)[0]),
             ("sequential-sum-snapshot-value",0,0,golden_wave(0,sequential=True)[0]),
             ("cross-half-sum-value",0,1,golden_wave(0,cross_half=True)[32]),
             ("wrong-boundary-sum-value",1,1,golden_wave(1)[0]))
    for name,warp,half,wrong in cases:
        require(wrong!=golden_wave(warp)[half*32],"Vacuous sum value control: "+name)
        result[name]=common+f"""example :
    (sourceWarp expWordOne true expWordOps (warpThreads (sourceGeometry expWordOne) 0 {warp}) sourceFuel.warp
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.memory ⟨.shared,0,1,{warp}*2+{half}⟩)=some (some {wrong}) := by
  rewrite [source_exp_wave_word_{warp}_{half}]
  decide
"""
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
    (project / "lakefile.toml").write_text('name = "native_softmax_exp_wave"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "check_exp_prefix.py", "check_exp_wave.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_exp_wave import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete native64 exponentiation/XOR-sum wave and inherited prefix/maximum-pass statement match.")
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
    execute("fresh-library-build", ["lake", "build", maximum.TARGET, base.TARGET], True)
    execute("fresh-exp-library-build", ["lake", "build", lane.TARGET], True)
    execute("fresh-wave-library-build", ["lake", "build", TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Exp-wave audits absent")
    for name, axioms in audits.items():
        require(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    mutations = controls(original, fixed, task, positive)
    for name, text in mutations.items():
        require(text != positive, "Vacuous control: " + name)
        (project / (name + ".lean")).write_text(text)
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    (project / "README.md").write_text(
        "Fresh checks: python3 validate_source.py; lake build. Other root Lean files intentionally fail.\n"
        "The maximum pass resumes both block barriers from the actual initializer.\n"
        "From that proved state each selected lane executes seven scalar exponential/sum rounds and parks at PC70.\n"
        "All valid exponential outputs and the unrounded source-ordered sum are proved, with the original fuel.\n"
        "Every native64 wave also executes all five source-ordered logical32 XOR/add stages, writes two partials and parks at PC82.\n"
        "The third barrier has not resumed; the block sum, normalization and whole launch remain open.\n"
        "Source certificates0. Canonical/IEEE equivalence and original-paper completion remain open.\n")
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
        "schema": 1, "status": "native-softmax-source-bound-exp-wave-checked", "stage": "exp-wave",
        "rows": {"min": 1, "max": native.MAX_ROWS}, "local_lean_modules": len(closure),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(mutations), "checks": checks,
        "actual_first_block_wave_fold_execution_proved": True, "starts_at_actual_initializer": True,
        "maximum_parked_pc": 42, "maximum_resumed_pc": 43, "maximum_block_epoch": 2,
        "physical_waves_per_block": 16, "threads_per_block": 1024, "logical_partials_per_block": 32,
        "accesses_per_maximum_pass": 57409, "input_reads_per_maximum_pass": 57344, "shared_writes_per_maximum_pass": 33, "shared_reads_per_maximum_pass": 32,
        "all32_source_ordered_partial_values_proved": True, "earlier_waves_preserved_proved": True,
        "first_barrier_resume_proved": True, "block_scheduler_decomposition_proved": True,
        "remaining_block_fuel_after_maximum": 3, "maximum_global_memory_frame_proved": True,
        "checksum_final_partial": maximum.block.golden_checksum(31), "checksum_row_maximum": maximum.golden_maximum(), "checksum_max_operation": "3*a+b",
        "checksum_final_partial_actual_fold_value_proved": True,
        "original_fuel": {"lane":4096,"warp":8,"block":5,"grid":1},
        "first_block_race_freedom_proved": True, "race_freedom_assumed": False,
        "actual_serial_block_wave_fold_execution_proved": True, "all32_serial_partial_reads_proved": True,
        "second_barrier_resume_proved": True, "maximum_pass_race_freedom_proved": True,
        "checksum_row_maximum_actual_fold_value_proved": True,
        "actual_exp_scalar_lane_prefix_execution_proved": True, "exp_starts_at_proved_maximum_state": True,
        "exp_parked_pc": 70, "exp_block_epoch": 2, "exp_outer_rounds": 7, "exp_components_per_round": 8,
        "exp_lane_costs": {"tid0_to80":982,"tid81_to1023":978},
        "exp_lane_access_increments": {"tid0_to80":213,"tid81_to1023":211},
        "exp_valid_stores_per_lane": {"tid0_to80":50,"tid81_to1023":49},
        "exp_converted_outputs_proved": True, "exp_unrounded_source_ordered_sum_proved": True,
        "exp_prefix_race_freedom_proved": True, "exp_native_indices_preserved_proved": True,
        "exp_word_model": WORD_MODEL, "exp_word_maximum": WORD_MAXIMUM,
        "exp_word_cases": {str(tid):golden_word(tid) for tid in WORD_TIDS},
        "exp_word_actual_sum_and_output_values_proved": True,
        "actual_exp_wave_fold_execution_proved": True, "actual_exp_block_phase_execution_proved": False,
        "exp_wave_parked_pc":82, "exp_wave_block_epoch":2, "exp_wave_logical_partials":2,
        "exp_wave_sum_stages":5, "exp_wave_shuffle_kind":"xor", "exp_wave_logical_width":32,
        "exp_wave_source_ordered_sum_proved":True, "exp_wave_snapshot_transport_proved":True,
        "exp_wave_partial_values_proved":True, "exp_wave_race_freedom_proved":True,
        "third_barrier_resume_proved":False, "serial_sum_execution_proved":False,
        "exp_wave_word_cases":{f"{warp}:{half}":golden_wave(warp)[half*32] for warp,half in WAVE_CASES},
        "exp_wave_word_actual_partial_values_proved":True,
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
