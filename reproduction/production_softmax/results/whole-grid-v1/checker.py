"""Fresh full-source repaired softmax grid execution and source-order correctness.

The complete original block remains checked. The new grid proof applies to
the repaired source only, under unchanged geometry/fuel and arbitrary Ops.
Canonical-real and IEEE bridges are separate validation stages.
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

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from reproduction.production_softmax import check_whole_block as block
from reproduction.production_softmax.prepare import source
from reproduction.production_softmax.grid_statement import EXTRA

HERE=Path(__file__).resolve().parent
TARGET="Lark.NativeSoftmaxCorrect"
maximum,base,prefix,native=block.maximum,block.base,block.prefix,block.native
lane,wave,reduction=block.lane,block.wave,block.reduction
sha,require=block.sha,block.require
WORD_TIDS,WORD_MAXIMUM,WORD_MODEL=block.WORD_TIDS,block.WORD_MAXIMUM,block.WORD_MODEL
golden_word,golden_wave,WAVE_CASES=block.golden_word,block.golden_wave,block.WAVE_CASES
PROJECTION_MODEL,projection_word,serial_checksum,whole_word=block.PROJECTION_MODEL,block.projection_word,block.serial_checksum,block.whole_word

def statement(original,fixed,task):
    return block.statement(original,fixed,task).replace("import Lark.NativeSoftmaxWholeBlock\n",
      "import Lark.NativeSoftmaxWholeBlock\nimport Lark.NativeSoftmaxCorrect\n",1)+"\n"+EXTRA

GRID_PRINCIPAL=set(re.findall(r"^theorem (\w+)",EXTRA,re.M)) | {
    'LarkNativeSoftmax.address_writer_row',
    'LarkNativeSoftmax.after_exp_foreign_epoch',
    'LarkNativeSoftmax.after_exp_foreign_pc',
    'LarkNativeSoftmax.after_maximum_foreign_epoch',
    'LarkNativeSoftmax.after_maximum_foreign_pc',
    'LarkNativeSoftmax.after_sum_foreign_epoch',
    'LarkNativeSoftmax.after_sum_foreign_pc',
    'LarkNativeSoftmax.exp_block_output_foreign',
    'LarkNativeSoftmax.first_block_foreign_pc',
    'LarkNativeSoftmax.fixed_block_fold_epoch_other',
    'LarkNativeSoftmax.fixed_block_fold_good',
    'LarkNativeSoftmax.fixed_block_fold_member_epoch',
    'LarkNativeSoftmax.fixed_block_fold_member_pc',
    'LarkNativeSoftmax.fixed_block_fold_output_member',
    'LarkNativeSoftmax.fixed_block_fold_output_other',
    'LarkNativeSoftmax.fixed_block_fold_pc_other',
    'LarkNativeSoftmax.fixed_block_fold_reads',
    'LarkNativeSoftmax.fixed_block_fold_run',
    'LarkNativeSoftmax.fixed_block_fold_trace_length',
    'LarkNativeSoftmax.fixed_grid_cut',
    'LarkNativeSoftmax.fixed_grid_epoch',
    'LarkNativeSoftmax.fixed_grid_fold_run',
    'LarkNativeSoftmax.fixed_grid_good',
    'LarkNativeSoftmax.fixed_grid_outputs',
    'LarkNativeSoftmax.fixed_grid_pc',
    'LarkNativeSoftmax.fixed_grid_reads',
    'LarkNativeSoftmax.fixed_grid_run',
    'LarkNativeSoftmax.fixed_grid_trace_length',
    'LarkNativeSoftmax.fixed_launch_run',
    'LarkNativeSoftmax.foreign_block_contains_false',
    'LarkNativeSoftmax.foreign_cohort_absent',
    'LarkNativeSoftmax.grid_halt_of_pc',
    'LarkNativeSoftmax.grid_rows_entry_tail',
    'LarkNativeSoftmax.initial_fixed_grid_extract',
    'LarkNativeSoftmax.initial_fixed_grid_flat_output',
    'LarkNativeSoftmax.initial_fixed_grid_output',
    'LarkNativeSoftmax.initial_fixed_grid_race_free',
    'LarkNativeSoftmax.initial_fixed_grid_trace_length',
    'LarkNativeSoftmax.initial_fixed_launch',
    'LarkNativeSoftmax.initial_grid_rows_entry',
    'LarkNativeSoftmax.maximum_foreign_epoch',
    'LarkNativeSoftmax.maximum_foreign_pc',
    'LarkNativeSoftmax.mid_foreign_epoch',
    'LarkNativeSoftmax.mid_foreign_pc',
    'LarkNativeSoftmax.norm_block_foreign_pc',
    'LarkNativeSoftmax.norm_block_output_foreign',
    'LarkNativeSoftmax.norm_block_reads',
    'LarkNativeSoftmax.norm_scalar_fold_input_memory',
    'LarkNativeSoftmax.norm_wave_fold_input_memory',
    'LarkNativeSoftmax.norm_wave_input_memory',
    'LarkNativeSoftmax.resume_foreign_epoch',
    'LarkNativeSoftmax.resume_foreign_pc',
    'LarkNativeSoftmax.source_extract_of_values',
    'LarkNativeSoftmax.source_order_correct',
    'LarkNativeSoftmax.source_ordered_spec_length',
    'LarkNativeSoftmax.sum_state_foreign_epoch',
    'LarkNativeSoftmax.sum_state_foreign_pc',
    'LarkNativeSoftmax.sum_state_output_foreign',
    'LarkNativeSoftmax.whole_block_entry_epoch',
    'LarkNativeSoftmax.whole_block_fixed_entry_other',
    'LarkNativeSoftmax.whole_block_foreign_epoch',
    'LarkNativeSoftmax.whole_block_foreign_pc',
    'LarkNativeSoftmax.whole_block_other_row_output',
    'LarkNativeSoftmax.whole_block_output_foreign',
    'LarkNativeSoftmax.whole_block_reads',
}
PRINCIPAL=block.PRINCIPAL | GRID_PRINCIPAL

def controls(original,fixed,task,positive):
    result={}
    for name,before,after in (
      ("grid-fixed-load-guard","norm_load_col < 50257","norm_load_col <= 50257"),
      ("grid-fixed-division","norm_value / total_sum","total_sum / norm_value"),
      ("grid-fixed-stride","norm_i = norm_i + 8192","norm_i = norm_i + 4096"),
    ):
        changed=fixed.replace(before,after,1)
        require(changed!=fixed,"Vacuous grid source control: "+name)
        # The inherited binding checks both complete source programs. A source
        # mutant is refused there before the later grid wrappers are needed.
        result[name]=maximum.block.statement(original,changed,task)
    common="import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    binders="""(p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat)
    (outside : Location → Option Nat)"""
    result["wrong-grid-halt"]=common+f"""example {binders}
    (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    (sourceFixedGrid p ops input outside).pc (row*1024+tid)=116 := by
  rewrite [source_fixed_grid_pc p ops input outside row tid hr ht]
  decide
"""
    result["wrong-grid-epoch"]=common+f"""example {binders}
    (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceFixedGrid p ops input outside).epochs (row*1024+tid)).block=5 := by
  rewrite [source_fixed_grid_epoch p ops input outside row tid hr ht]
  decide
"""
    result["invented-grid-none"]=common+f"""example {binders} :
    (sourceLaunch p true ops (sourceInitial p input outside)).isSome=false := by
  rewrite [source_fixed_grid_launch p ops input outside]
  simp only [Option.isSome_some]
  decide
"""
    result["invented-grid-race"]=common+f"""example {binders} :
    raceFree (sourceGeometry p) (sourceFixedGrid p ops input outside).trace=false := by
  rewrite [source_fixed_grid_rf p ops input outside]
  decide
"""
    result["missing-grid-output"]=common+f"""example {binders}
    (offset : Nat) (ho : offset<p.rows*50257) :
    ((sourceFixedGrid p ops input outside).memory (globalCell 0 offset)).isSome=false := by
  rewrite [source_fixed_grid_output p ops input outside offset ho]
  simp only [Option.isSome_some]
  decide
"""
    result["missing-grid-extraction"]=common+f"""example {binders} :
    (extract (sourceLayout p) (sourceFixedGrid p ops input outside)).isSome=false := by
  rewrite [source_fixed_grid_extract p ops input outside]
  simp only [Option.isSome_some]
  decide
"""
    result["denied-grid-trace-count"]=common+f"""example {binders} :
    ((sourceFixedGrid p ops input outside).trace.length == 475752*p.rows)=false := by
  rewrite [source_fixed_grid_trace p ops input outside]
  simp only [beq_self_eq_true]
  decide
"""
    result["denied-grid-output-length"]=common+"""example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat) :
    ((sourceOrderedSpec p ops input).length == p.rows*50257)=false := by
  rewrite [source_ordered_spec_length]
  simp only [beq_self_eq_true]
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
    (project / "lakefile.toml").write_text('name = "native_softmax_whole_grid"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "check_exp_prefix.py", "check_exp_wave.py", "check_reduction_prefix.py", "reduction_statement.py", "check_whole_block.py", "whole_block_statement.py", "check_whole_grid.py", "grid_statement.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_whole_grid import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and complete repaired-grid execution, source-order correctness and all inherited statements match.")
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
    execute("fresh-wave-library-build", ["lake", "build", wave.TARGET], True)
    execute("fresh-reduction-library-build", ["lake", "build", reduction.TARGET], True)
    execute("fresh-grid-library-build", ["lake", "build", TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Whole-grid audits absent")
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
        "All16 exp waves and all16 serial-sum waves execute; both later block barriers resume through PC93/epoch4.\n"
        "The constructive four-phase prefix returns Some and links to runBlock with its original one remaining phase.\n"
        "All50257 converted exp outputs and the unrounded source-ordered row total are retained.\n"
        "Normalization executes all16 waves, halts all1024 lanes, and retains all50257 converted division outputs.\n"
        "The repaired actual whole block trace is classified Good and proved race-free.\n"
        "The repaired full grid returns Some, is race-free and extracts all source-ordered outputs. Original conflict reachability and canonical/IEEE bridges remain open.\n"
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
        "schema": 1, "status": "native-softmax-source-bound-whole-grid-checked", "stage": "whole-grid",
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
        "actual_exp_wave_fold_execution_proved": True, "actual_exp_block_phase_execution_proved": True,
        "exp_wave_parked_pc":82, "exp_wave_block_epoch":2, "exp_wave_logical_partials":2,
        "exp_wave_sum_stages":5, "exp_wave_shuffle_kind":"xor", "exp_wave_logical_width":32,
        "exp_wave_source_ordered_sum_proved":True, "exp_wave_snapshot_transport_proved":True,
        "exp_wave_partial_values_proved":True, "exp_wave_race_freedom_proved":True,
        "third_barrier_resume_proved":True, "serial_sum_execution_proved":True,
        "exp_wave_word_cases":{f"{warp}:{half}":golden_wave(warp)[half*32] for warp,half in WAVE_CASES},
        "exp_wave_word_actual_partial_values_proved":True,
        "actual_reduction_prefix_some_execution_proved":True, "reduction_prefix_linked_to_runBlock":True,
        "fourth_barrier_resume_proved":True, "reduction_phases":4, "reduction_parked_pc":92,
        "reduction_resumed_pc":93, "reduction_block_epoch":4, "remaining_block_fuel_after_sum":1,
        "accesses_per_exp_block_phase":216258, "accesses_after_third_barrier":273667,
        "shared_reads_per_serial_sum_phase":32, "shared_writes_per_serial_sum_phase":1,
        "accesses_after_fourth_barrier":273700,
        "all32_exp_partial_values_proved":True, "all32_serial_sum_partial_reads_proved":True,
        "source_ordered_row_sum_proved":True, "all_exponential_output_values_preserved_proved":True,
        "reduction_prefix_race_freedom_proved":True,
        "reduction_projection_model":PROJECTION_MODEL, "reduction_projection_values":projection_word(),
        "reduction_projection_actual_full_prefix_values_proved":True,
        "serial_checksum_model":"7*a+b, slots1..32", "serial_checksum":serial_checksum(),
        "serial_checksum_isolated_actual_phase_proved":True,
        "serial_checksum_scope":"Synthetic PC83/epoch3 entry for the actual serial phase; separate from the full-prefix projection witness.",
        "normalization_execution_proved":True,
        "actual_whole_block_some_execution_proved":True, "all_five_source_block_phases_proved":True,
        "whole_block_source_ordered_outputs_proved":True, "whole_block_source_initializer_bound":True,
        "repaired_whole_block_trace_classification_proved":True, "repaired_whole_block_race_freedom_proved":True,
        "original_whole_block_race_freedom_proved":False, "whole_grid_execution_proved":True,
        "normalization_outer_rounds":7, "normalization_components_per_round":8, "whole_block_epoch":4,
        "whole_block_halt_pc":{"original":116,"fixed":115},
        "normalization_lane_costs":{"original":{"tid0_to80":880,"tid81_to1023":878},"fixed":{"tid0_to80":862,"tid81_to1023":857}},
        "normalization_lane_accesses":{"original":{"tid0_to80":213,"tid81_to1023":211},"fixed":{"tid0_to80":201,"tid81_to1023":197}},
        "normalization_block_accesses":{"original":216226,"fixed":202052},
        "whole_block_accesses":{"original":489926,"fixed":475752},
        "whole_block_word":whole_word(), "whole_block_actual_converted_output_values_proved":True,

        "source_certificates": 0, "whole_kernel_execution_proved": True,
        "conflict_witness_state_reachability_proved": False, "actual_trace_universal_classification_proved": False,
        "canonical_source_equivalence_proved": False, "ieee_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    report.update({
        "whole_grid_variants":["fixed"], "original_whole_grid_execution_proved":False,
        "repaired_whole_grid_some_execution_proved":True, "repaired_whole_grid_race_freedom_proved":True,
        "repaired_whole_grid_trace_classification_proved":True,
        "repaired_whole_grid_all_outputs_proved":True, "repaired_whole_grid_extract_proved":True,
        "repaired_whole_grid_source_order_correct_proved":True,
        "whole_grid_source_initializer_bound":True, "foreign_block_control_and_memory_frames_proved":True,
        "grid_halt_pc":115, "grid_block_epoch":4, "grid_accesses_per_row":475752,
        "grid_output_cells_per_row":50257, "grid_all_supported_rows_proved":True,
        "inherited_block_controls_previously_rejected":129,
        "inherited_block_evidence":"results/whole-block-v1 and whole-block-validation-v1; not counted again in this packet's false claims",
        "scope":"Actual repaired complete grid under arbitrary Ops; original source complete block only. No algebraic rearrangement, canonical-real or IEEE bridge asserted here.",
    })
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(closure), "audits": len(audits), "rejections": len(mutations)}))


if __name__ == "__main__":
    main()
