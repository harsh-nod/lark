"""Fresh source-bound complete native softmax block execution.

Both full sources execute all five phases and retain every converted output.
The repaired actual block trace is proved race-free. Grid composition,
original conflict reachability and canonical/IEEE reference bridges stay open.
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
from reproduction.production_softmax import check_reduction_prefix as reduction  # noqa: E402
wave = reduction.wave
from reproduction.production_softmax.prepare import source  # noqa: E402

maximum = wave.maximum
lane = wave.lane
base, prefix, native = wave.base, wave.prefix, wave.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxWholeBlock"
sha, require = maximum.sha, maximum.require


from reproduction.production_softmax.whole_block_statement import EXTRA  # noqa: E402

WORD_TIDS, WORD_MAXIMUM, WORD_MODEL = wave.WORD_TIDS, wave.WORD_MAXIMUM, wave.WORD_MODEL
golden_word = wave.golden_word
golden_wave, WAVE_CASES = wave.golden_wave, wave.WAVE_CASES
PROJECTION_MODEL = {"max":"right projection","add":"right projection","sub":"2*a+b",
                    "exp":"5*a+3","fromHalf":"3*a+1","toHalf":"7*a+1"}


def projection_word():
    maximum=3*(50256+1)+1
    scalar=[]
    for tid in range(1024):
        total=0
        for linear in range(56):
            col=tid+linear*1024
            if col<50257:
                total=5*(2*(3*(col+1)+1)+maximum)+3
        scalar.append(total)
    partials=[]
    for warp in range(16):
        values=scalar[warp*64:(warp+1)*64]
        for mask in (16,8,4,2,1):
            old=values.copy()
            values=[old[(lane//32)*32+((lane%32)^mask)] for lane in range(64)]
        partials.extend((values[0],values[32]))
    return {"maximum":maximum,"total":partials[-1],
            "outputs":{str(col):7*(5*(2*(3*(col+1)+1)+maximum)+3)+1 for col in (0,50256)}}


def serial_checksum(*, reverse=False, omit_last=False):
    total=1
    for slot in range(1,31 if omit_last else 32):
        total=7*(slot+1)+total if reverse else 7*total+(slot+1)
    return total


WHOLE_PRINCIPAL = set(re.findall(r"^theorem (\w+)",EXTRA,re.M)) | {
    "LarkNativeSoftmax.initial_whole_block", "LarkNativeSoftmax.whole_block_run",
    "LarkNativeSoftmax.whole_block_outputs", "LarkNativeSoftmax.initial_whole_block_trace_length",
    "LarkNativeSoftmax.initial_whole_block_fixed_race_free", "LarkNativeSoftmax.norm_block_run",
    "LarkNativeSoftmax.norm_block_outputs", "LarkNativeSoftmax.norm_block_accesses",
    "LarkNativeSoftmax.norm_wave_run", "LarkNativeSoftmax.norm_wave_fold_run",
    "LarkNativeSoftmax.norm_scalar_fold_run", "LarkNativeSoftmax.norm_lane_run",
    "LarkNativeSoftmax.norm_lane_cost_exact", "LarkNativeSoftmax.norm_lane_trace_exact",
    "LarkNativeSoftmax.norm_lane_entry_other", "LarkNativeSoftmax.norm_sample_of_present",
    "LarkNativeSoftmax.norm_load_component_eq", "LarkNativeSoftmax.norm_store_component_eq",
}
PRINCIPAL = reduction.PRINCIPAL | WHOLE_PRINCIPAL


def statement(original,fixed,task):
    return reduction.statement(original,fixed,task).replace("import Lark.NativeSoftmaxReductionPrefix\n",
        "import Lark.NativeSoftmaxReductionPrefix\nimport Lark.NativeSoftmaxWholeBlock\n",1)+"\n"+EXTRA


def whole_word():
    values=projection_word()
    return {"model":{**PROJECTION_MODEL,"div":"Nat floor division"},"total":values["total"],
            "outputs":{col:7*((3*value+1)//values["total"])+1 for col,value in values["outputs"].items()}}


def controls(original,fixed,task,positive):
    result=reduction.controls(original,fixed,task,reduction.statement(original,fixed,task))
    for name,which,before,after in (
        ("norm-denominator-slot","original","float total_sum = sumvals[0];","float total_sum = sumvals[1];"),
        ("norm-private-source","original","float norm_value = norm_regs[norm_store_u];","float norm_value = exp_regs[norm_store_u];"),
        ("norm-output-from-input","original","__half2float(out[norm_load_address])","__half2float(inp[norm_load_address])"),
        ("norm-extra-half-round-trip","original","__half2float(out[norm_load_address])","__half2float(__float2half(__half2float(out[norm_load_address])))"),
        ("norm-missing-division","original","__float2half(norm_value / total_sum)","__float2half(norm_value)"),
        ("norm-reversed-division","original","norm_value / total_sum","total_sum / norm_value"),
        ("norm-multiplied-value","original","norm_value / total_sum","norm_value * total_sum"),
        ("norm-clamp-changed","original","norm_load_col = 50256","norm_load_col = 50255"),
        ("norm-load-components-omitted","original","norm_load_u < 8","norm_load_u < 7"),
        ("norm-store-components-omitted","original","norm_store_u < 8","norm_store_u < 7"),
        ("norm-stride-changed","original","norm_i = norm_i + 8192","norm_i = norm_i + 4096"),
        ("norm-store-guard-changed","original","norm_store_col < 50257","norm_store_col <= 50257"),
        ("norm-fixed-load-guard-changed","fixed","norm_load_col < 50257","norm_load_col <= 50257"),
    ):
        text=original if which=="original" else fixed
        changed=text.replace(before,after,1)
        require(changed!=text,"Vacuous normalization source control: "+name)
        try:
            result[name]=maximum.block.statement(changed if which=="original" else original,
                changed if which=="fixed" else fixed,task)
        except Exception as error:
            raise ValueError("Normalization source control did not translate: "+name) from error
    common="import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    for name,guarded,wrong in (("wrong-whole-fixed-halt","true",116),("wrong-whole-original-halt","false",115)):
        result[name]=common+f"""example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat)
    (outside : Location → Option Nat) (row tid : Nat) (ht : tid<1024) :
    (sourceWholeBlock p {guarded} ops input outside row).pc (row*1024+tid)={wrong} := by
  rewrite [source_whole_block_pc p {guarded} ops input outside row tid ht]
  decide
"""
    result["wrong-whole-epoch"]=common+"""example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat)
    (outside : Location → Option Nat) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceWholeBlock p true ops input outside row).epochs (row*1024+tid)).block=5 := by
  rewrite [source_whole_block_epoch p true ops input outside row tid hr ht]
  decide
"""
    for name,guarded,wrong in (("wrong-whole-fixed-trace","true",475751),("wrong-whole-original-trace","false",489925)):
        result[name]=common+f"""example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat)
    (outside : Location → Option Nat) (row : Nat) :
    (sourceWholeBlock p {guarded} ops input outside row).trace.length={wrong} := by
  rewrite [source_whole_block_trace]
  decide
"""
    result["invented-whole-block-none"]=common+"""example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat)
    (outside : Location → Option Nat) (row : Nat) (hr : row<p.rows) :
    (sourceBlock p true ops row sourceFuel.block (sourceInitial p input outside)).isSome=false := by
  rewrite [source_whole_block_run p true ops input outside row hr]
  change true=false
  decide
"""
    for name,wrong in (("whole-output-left-exponential",5277322),("whole-output-reversed-division",1),
                       ("whole-output-without-from-half",15),("whole-output-without-to-half",7)):
        result[name]=common+f"""example :
    (sourceBlock expWordOne true reductionProjectionOps 0 sourceFuel.block
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map
        (fun s => s.memory (globalCell 0 (address 0 0)))=some (some {wrong}) := by
  rewrite [source_whole_projection_output_0]
  decide
"""
    result["wrong-whole-boundary-output"]=common+"""example :
    (sourceBlock expWordOne false reductionProjectionOps 0 sourceFuel.block
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map
        (fun s => s.memory (globalCell 0 (address 0 50256)))=some (some 147) := by
  rewrite [source_whole_projection_output_50256]
  decide
"""
    for name,guarded,wrong in (("wrong-norm-fixed-cost","true",858),("wrong-norm-original-cost","false",879)):
        result[name]=common+f"""example : normLaneCost {guarded} 81={wrong} := by
  rewrite [source_normalization_lane_cost {guarded} 81 (by decide)]
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
    (project / "lakefile.toml").write_text('name = "native_softmax_whole_block"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "check_exp_prefix.py", "check_exp_wave.py", "check_reduction_prefix.py", "reduction_statement.py", "check_whole_block.py", "whole_block_statement.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_whole_block import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and complete five-phase block execution, converted outputs and all inherited statements match.")
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
    execute("fresh-normalization-library-build", ["lake", "build", TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Whole-block audits absent")
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
        "Grid composition, original conflict reachability and canonical/IEEE bridges remain open.\n"
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
        "schema": 1, "status": "native-softmax-source-bound-whole-block-checked", "stage": "whole-block",
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
        "original_whole_block_race_freedom_proved":False, "whole_grid_execution_proved":False,
        "normalization_outer_rounds":7, "normalization_components_per_round":8, "whole_block_epoch":4,
        "whole_block_halt_pc":{"original":116,"fixed":115},
        "normalization_lane_costs":{"original":{"tid0_to80":880,"tid81_to1023":878},"fixed":{"tid0_to80":862,"tid81_to1023":857}},
        "normalization_lane_accesses":{"original":{"tid0_to80":213,"tid81_to1023":211},"fixed":{"tid0_to80":201,"tid81_to1023":197}},
        "normalization_block_accesses":{"original":216226,"fixed":202052},
        "whole_block_accesses":{"original":489926,"fixed":475752},
        "whole_block_word":whole_word(), "whole_block_actual_converted_output_values_proved":True,

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
