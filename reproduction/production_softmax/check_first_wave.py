"""Fresh source-bound native softmax maximum wave through the first barrier.

Both full source variants retain their declared fuel and machine semantics.
This stage proves no whole launch or softmax reference-equivalence result.
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
from reproduction.production_softmax import check_prefix as prefix  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

base, native = prefix.base, prefix.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxMaxWaveTree"
sha, require = prefix.sha, prefix.require


def statement(original, fixed, task):
    text = prefix.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxMaxPrefixCost\n",
        "import Lark.NativeSoftmaxMaxPrefixCost\nimport Lark.NativeSoftmaxMaxWaveTree\n", 1)
    text += '''
def sourceWarp (p : Shape) (guarded : Bool) (ops : Ops α) (ts : List Nat) (budget : Nat)
    (s : State α) : Option (State α) :=
  LarkPartitionCollective.runWarp ops (sourceLayout p) (sourceGeometry p) sourceFuel
    (if guarded then sourceFixed else sourceOriginal) ts budget s
def sourceWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) : State α :=
  firstWave p ops input row warp (sourceInitial p input outside)
theorem source_warp_data (p : Shape) (guarded : Bool) (ops : Ops α) (ts : List Nat)
    (budget : Nat) (s : State α) :
    sourceWarp p guarded ops ts budget s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded) ts budget s := by
  simp only [sourceWarp,program,source_program_data.1,source_program_data.2,
    (source_interface_data p).1,(source_interface_data p).2.1,(source_interface_data p).2.2]
theorem source_wave_initial_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row warp : Nat)
    (hr : row < p.rows) (hw : warp < 16) :
    sourceWarp p guarded ops (warpThreads (sourceGeometry p) row warp) sourceFuel.warp
      (sourceInitial p input outside) = some (sourceWave p ops input outside row warp) := by
  rewrite [source_warp_data,(source_interface_data p).2.1,(source_interface_data p).2.2,source_initial_data]
  exact first_wave_initial p guarded ops input outside row warp hr hw
theorem source_wave_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat) (hl : lane < 64) :
    (sourceWave p ops input outside row warp).pc (cohortBase row warp+lane) = 32 :=
  first_wave_pc p ops input row warp _ lane hl
theorem source_wave_initial_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp half : Nat) (hw : warp < 16) (hh : half < 2) :
    (sourceWave p ops input outside row warp).memory ⟨.shared,row,0,warp*2+half⟩ =
      some (downTree ops.max (fun lane => threadMaximum ops input row (warp*64+lane)) 5 (half*32)) :=
  first_wave_partial_tree p ops input row warp half _ hw hh
theorem source_wave_initial_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    (sourceWave p ops input outside row warp).epochs = (sourceInitial p input outside).epochs :=
  first_wave_epochs p ops input row warp _
theorem source_wave_initial_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (l : Location)
    (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (sourceWave p ops input outside row warp).memory l = (sourceInitial p input outside).memory l :=
  first_wave_memory_frame p ops input row warp _ l hl
theorem source_wave_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    ∀ a ∈ (sourceWave p ops input outside row warp).trace, Good a :=
  first_wave_initial_good p ops input outside row warp
theorem source_wave_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    raceFree (sourceGeometry p) (sourceWave p ops input outside row warp).trace = true := by
  rewrite [(source_interface_data p).2.1]
  exact first_wave_initial_race_free p ops input outside row warp
theorem source_wave_initial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hw : warp < 16) :
    (sourceWave p ops input outside row warp).trace.length = 3586 :=
  first_wave_trace_length p ops input row warp _ hw
theorem source_memory_of_run (run : Option (State α)) (final : State α) (l : Location)
    (value : α) (hr : run = some final) (hv : final.memory l = some value) :
    run.map (fun s => s.memory l) = some (some value) := by
  rewrite [hr]
  change some (final.memory l) = some (some value)
  rewrite [hv]
  rfl
theorem source_wave_initial_partial_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (row warp half : Nat)
    (hr : row < p.rows) (hw : warp < 16) (hh : half < 2) :
    (sourceWarp p guarded ops (warpThreads (sourceGeometry p) row warp) sourceFuel.warp
      (sourceInitial p input outside)).map (fun s => s.memory ⟨.shared,row,0,warp*2+half⟩) =
        some (some (downTree ops.max (fun lane => threadMaximum ops input row (warp*64+lane)) 5 (half*32))) :=
  source_memory_of_run _ _ _ _ (source_wave_initial_run p guarded ops input outside row warp hr hw)
    (source_wave_initial_partial p ops input outside row warp half hw hh)
'''
    for name in ("source_warp_data", "source_wave_initial_run", "source_wave_initial_pc",
                 "source_wave_initial_partial", "source_wave_initial_epochs", "source_wave_initial_memory_frame",
                 "source_wave_initial_good", "source_wave_initial_rf", "source_wave_initial_trace_length",
                 "source_memory_of_run", "source_wave_initial_partial_run"):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    result = prefix.controls(original, fixed, task, prefix.statement(original, fixed, task))
    for name, before, after in (
        ("changed-last-max-distance", "__shfl_down(maxval, 1, 32)", "__shfl_down(maxval, 2, 32)"),
        ("changed-logical-width", "__shfl_down(maxval, 16, 32)", "__shfl_down(maxval, 16, 64)"),
        ("swapped-shuffle-max-operands", "fmaxf(maxval, max_other)", "fmaxf(max_other, maxval)"),
        ("changed-partial-leader", "if (lane_id == 0)", "if (lane_id == 1)"),
        ("changed-partial-slot", "maxvals[warp_id] = maxval", "maxvals[0] = maxval"),
        ("changed-partial-bank", "maxvals[warp_id] = maxval", "sumvals[warp_id] = maxval"),
        ("omitted-first-block-barrier", "__syncthreads();", ""),
    ):
        changed = original.replace(before, after, 1)
        require(changed != original, "Vacuous source control: " + name)
        result[name] = statement(changed, fixed, task)
    common = "import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-wave-endpoint"] = common + '''example :
    (sourceWave prefixOne wordOps wordInput (fun _ => none) 0 0).pc (cohortBase 0 0+0) = 33 := by
  rewrite [source_wave_initial_pc prefixOne wordOps wordInput (fun _ => none) 0 0 0 (by decide)]
  decide
'''
    result["wrong-wave-trace-length"] = common + '''example :
    (sourceWave prefixOne wordOps wordInput (fun _ => none) 0 0).trace.length = 3584 := by
  rewrite [source_wave_initial_trace_length prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide)]
  decide
'''
    result["invented-shuffle-fence"] = common + '''example :
    ((sourceWave prefixOne wordOps wordInput (fun _ => none) 0 0).epochs 0).block = 1 := by
  rewrite [source_wave_initial_epochs]
  change 0 = 1
  decide
'''
    result["wrong-source-warp-fuel"] = positive.replace(
        "def sourceFuel : Fuel := ⟨4096,8,5,1⟩", "def sourceFuel : Fuel := ⟨4096,7,5,1⟩", 1) + "\nexample : sourceFuel.warp = 8 := by decide\n"
    for name, claim in {
        "cross-logical-partition-peer": "downPeer32 31 16 = 47",
        "dropped-overflow-self-update": "downLeaves 5 31 = [31]",
        "wrong-leaf-order": "downLeaves 5 0 = List.range 32",
        "wrong-second-half-leaves": "downLeaves 5 32 = downLeaves 5 0",
    }.items():
        result[name] = common + f"example : {claim} := by decide\n"
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
    (project / "lakefile.toml").write_text('name = "native_softmax_max_first_wave"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_first_wave import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete maximum-wave statement match.")
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
                    and "maximum heartbeats" not in log, "Wrong rejection gate: " + name)
        checks.append({"name": name, "expected_accepted": expected, "accepted": accepted,
                       "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
        return log

    execute("frozen-reader", [sys.executable, "validate_source.py"], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require({"source_wave_initial_run", "source_wave_initial_partial_run", "source_wave_initial_good",
             "source_wave_initial_rf", "source_wave_initial_trace_length", "source_wave_initial_epochs",
             "LarkNativeSoftmax.first_wave_initial", "LarkNativeSoftmax.first_wave_partial_tree",
             "LarkNativeSoftmax.down_leaves_cover", "LarkNativeSoftmax.first_wave_trace_length"} <= audits.keys(),
            "First-wave audits absent")
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
        "Both full source variants execute a physical wave64 from entry to the first block barrier PC32.\n"
        "The two logical32 groups retain their exact down/max trees, 3584 input reads and two shared stores.\n"
        "Race freedom, global-memory frames and unchanged epochs are proved for the first wave.\n"
        "Block/grid composition, later passes, the complete launch and reference bridge remain open. Source certificates0.\n")
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
        "schema": 1, "status": "native-softmax-source-bound-maximum-first-wave-checked", "stage": "max-first-wave",
        "rows": {"min": 1, "max": native.MAX_ROWS}, "local_lean_modules": len(closure),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(mutations), "checks": checks,
        "actual_maximum_wave_execution_proved": True, "starts_at_actual_initializer": True,
        "endpoint_pc": 32, "physical_wave_width": 64, "logical_partition_width": 32,
        "accesses_per_wave": 3586, "input_reads_per_wave": 3584, "shared_writes_per_wave": 2,
        "source_ordered_maximum_tree_proved": True, "two_distinct_partial_values_proved": True,
        "global_memory_frame_proved": True, "epochs_preserved_proved": True,
        "original_fuel": {"lane":4096,"warp":8,"block":5,"grid":1},
        "first_wave_race_freedom_proved": True, "race_freedom_assumed": False,
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
