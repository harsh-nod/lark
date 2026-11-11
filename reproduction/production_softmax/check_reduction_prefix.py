"""Fresh source-bound native softmax scalar exponentiation/sum prefix.

The full1024-thread maximum, exponential/XOR sum and serial sum phases
execute constructively from the initializer through PC93/epoch4. Normalization stays open;
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
from reproduction.production_softmax import check_exp_wave as wave  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

maximum = wave.maximum
lane = wave.lane
base, prefix, native = wave.base, wave.prefix, wave.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxReductionPrefix"
sha, require = maximum.sha, maximum.require


from reproduction.production_softmax.reduction_statement import EXTRA  # noqa: E402

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


REDUCTION_PRINCIPAL = set(re.findall(r"^theorem (\w+)",EXTRA,re.M)) | {
    "LarkNativeSoftmax.reduction_prefix_run", "LarkNativeSoftmax.initial_reduction_prefix",
    "LarkNativeSoftmax.reduction_phase_continue", "LarkNativeSoftmax.reduction_prefix_continue",
    "LarkNativeSoftmax.exp_block_fold_run", "LarkNativeSoftmax.exp_block_partial",
    "LarkNativeSoftmax.initial_exp_barrier", "LarkNativeSoftmax.initial_after_exp_trace_length",
    "LarkNativeSoftmax.sum_serial_block_fold_run", "LarkNativeSoftmax.sum_serial_block_value",
    "LarkNativeSoftmax.initial_sum_ready", "LarkNativeSoftmax.initial_sum_block",
    "LarkNativeSoftmax.initial_sum_trace_length", "LarkNativeSoftmax.initial_sum_race_free",
    "LarkNativeSoftmax.sum_state_outputs", "LarkNativeSoftmax.exp_block_outputs",
}
PRINCIPAL=wave.PRINCIPAL | REDUCTION_PRINCIPAL


def statement(original,fixed,task):
    return wave.statement(original,fixed,task).replace("import Lark.NativeSoftmaxExpWave\n",
        "import Lark.NativeSoftmaxExpWave\nimport Lark.NativeSoftmaxReductionPrefix\n",1)+"\n"+EXTRA


def controls(original,fixed,task,positive):
    result=wave.controls(original,fixed,task,wave.statement(original,fixed,task))
    for name,before,after in (
        ("changed-sum-serial-leader","if (tid == 0) {\nfloat block_sum","if (tid == 1) {\nfloat block_sum"),
        ("changed-sum-serial-bound","sum_warp < 32","sum_warp < 31"),
        ("changed-sum-serial-start","int sum_warp = 1","int sum_warp = 0"),
        ("swapped-sum-serial-operands","block_sum = block_sum + warp_sum","block_sum = warp_sum + block_sum"),
        ("changed-sum-serial-store","sumvals[0] = block_sum","sumvals[31] = block_sum"),
        ("omitted-fourth-block-barrier","sumvals[0] = block_sum;\n}\n__syncthreads();","sumvals[0] = block_sum;\n}"),
    ):
        changed=original.replace(before,after,1)
        require(changed!=original,"Vacuous serial source control: "+name)
        result[name]=maximum.block.statement(changed,fixed,task)
    common="import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-reduction-endpoint"]=common+'''example :
    (sourceSumState expWordOne expWordOps expWordInput (fun _ => none) 0).pc (0*1024+0)=94 := by
  rewrite [source_sum_initial_pc expWordOne expWordOps expWordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-fourth-barrier-epoch"]=common+'''example :
    ((sourceSumState expWordOne expWordOps expWordInput (fun _ => none) 0).epochs (0*1024+0)).block=3 := by
  rewrite [source_sum_initial_epoch expWordOne expWordOps expWordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-reduction-access-count"]=common+'''example :
    (sourceSumState expWordOne expWordOps expWordInput (fun _ => none) 0).trace.length=273667 := by
  rewrite [source_sum_initial_trace]
  decide
'''
    result["invented-reduction-none"]=common+'''example :
    (sourceReductionPrefix expWordOne false reductionProjectionOps 0 4
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).isSome=false := by
  rewrite [source_reduction_initial_run expWordOne false reductionProjectionOps reductionProjectionInput (fun _ => none) 0 (by decide)]
  change true=false
  decide
'''
    word=projection_word()
    for name,wrong in (("wrong-reduction-total",0),("rounded-reduction-total",7*word["total"]+1)):
        require(wrong!=word['total'],"Vacuous total control")
        result[name]=common+f'''example :
    (sourceReductionPrefix expWordOne true reductionProjectionOps 0 4
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map (fun s => s.memory ⟨.shared,0,1,0⟩)=
      some (some {wrong}) := by
  rewrite [source_reduction_projection_total]
  decide
'''
    result["wrong-preserved-exp-output"]=common+'''example :
    (sourceReductionPrefix expWordOne true reductionProjectionOps 0 4
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map
        (fun s => s.memory (globalCell 0 (address 0 50256)))=some (some 2261583) := by
  rewrite [source_reduction_projection_output_50256]
  decide
'''
    for name,wrong in (("reversed-serial-sum-value",serial_checksum(reverse=True)),
                       ("omitted-final-serial-sum-value",serial_checksum(omit_last=True))):
        require(wrong!=serial_checksum(),"Vacuous serial value control")
        result[name]=common+f'''example :
    (sourceBlockFold expWordOne true expWordOps 0 sumChecksumState).map
      (fun s => s.memory ⟨.shared,0,1,0⟩)=some (some {wrong}) := by
  rewrite [source_sum_checksum_run]
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
    (project / "lakefile.toml").write_text('name = "native_softmax_reduction_prefix"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "check_exp_prefix.py", "check_exp_wave.py", "check_reduction_prefix.py", "reduction_statement.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_reduction_prefix import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete constructive four-phase reduction prefix and all inherited statements match.")
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
    execute("fresh-reduction-library-build", ["lake", "build", TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Reduction-prefix audits absent")
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
        "Normalization, whole launch and canonical/IEEE reference bridges remain open.\n"
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
        "schema": 1, "status": "native-softmax-source-bound-reduction-prefix-checked", "stage": "reduction-prefix",
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
        "normalization_execution_proved":False,

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
