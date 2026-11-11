"""Check the full source's actual first maximum prefix in a fresh Lean project.

The source-bound result stops before the first logical32 shuffle. It establishes
no complete launch, reference equivalence or source certificate.
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
from lark_kernels import native_softmax as native  # noqa: E402
from reproduction.production_softmax import check_program as base  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxMaxPrefixCost"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def golden_word(tid, *, clamp=50256, count=56, cast=True, reverse=False, seed=3):
    values = [min(clamp, tid + component * 1024) for component in range(count)]
    if reverse:
        values.reverse()
    return [seed] + [item for value in values for item in ([1, 2, value] if cast else [1, value])]


def statement(original, fixed, task):
    text = base.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxWitness\n",
        "import Lark.NativeSoftmaxWitness\nimport Lark.NativeSoftmaxMaxPrefixCost\n", 1)
    text += '''
def sourceInitial (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  initial (sourceLayout p) input outside
def sourceLane (p : Shape) (guarded : Bool) (ops : Ops α) (t budget : Nat) (s : State α) : Option (State α) :=
  LarkCollective.runLane ops (sourceLayout p) (sourceGeometry p)
    (if guarded then sourceFixed else sourceOriginal) t budget s
theorem source_lane_data (p : Shape) (guarded : Bool) (ops : Ops α) (t budget : Nat) (s : State α) :
    sourceLane p guarded ops t budget s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t budget s := by
  simp only [sourceLane,program,source_program_data.1,source_program_data.2,
    (source_interface_data p).1,(source_interface_data p).2.1]
theorem source_initial_data (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    sourceInitial p input outside = initial (layout p) input outside := rfl
theorem source_prefix_initial_run (p : Shape) (guarded : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) (ht : t < p.rows*1024) :
    sourceLane p guarded ops t sourceFuel.lane (sourceInitial p input outside) =
      some (maxPrefixState ops input t (sourceInitial p input outside)) := by
  rewrite [source_lane_data,source_initial_data,(source_interface_data p).2.2]
  exact initial_max_prefix_run p guarded ops input outside t ht
theorem source_prefix_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (maxPrefixState ops input t (sourceInitial p input outside)).pc t = 20 :=
  max_prefix_pc ops input t _
theorem source_prefix_initial_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (maxPrefixState ops input t (sourceInitial p input outside)).regs t 0 =
      some (threadMaximum ops input (t/1024) (t%1024)) := by
  rewrite [source_initial_data]
  exact initial_max_prefix_value p ops input outside t
theorem source_prefix_initial_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (maxPrefixState ops input t (sourceInitial p input outside)).memory = (sourceInitial p input outside).memory ∧
    (maxPrefixState ops input t (sourceInitial p input outside)).epochs = (sourceInitial p input outside).epochs ∧
    (maxPrefixState ops input t (sourceInitial p input outside)).trace.length = 56 := by
  have frame := max_prefix_frames ops input t (sourceInitial p input outside)
  exact ⟨frame.1,frame.2.1,by simpa only [sourceInitial,initial,List.length_nil,Nat.zero_add] using frame.2.2⟩
theorem source_prefix_initial_inputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (maxPrefixState ops input t (sourceInitial p input outside)).trace, MaxInputAccess a := by
  rewrite [source_initial_data]
  exact initial_max_prefix_inputs p ops input outside t
theorem source_prefix_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    raceFree (sourceGeometry p) (maxPrefixState ops input t (sourceInitial p input outside)).trace = true := by
  rewrite [source_initial_data,(source_interface_data p).2.1]
  exact initial_max_prefix_race_free p ops input outside t
theorem source_prefix_cost (tid : Nat) (ht : tid < 1024) :
    maxPrefixCost tid = if tid < 81 then 497 else 498 := max_prefix_cost_exact tid ht
theorem source_register_of_run (run : Option (State α)) (final : State α) (t : Nat) (value : α)
    (hr : run = some final) (hv : final.regs t 0 = some value) :
    run.map (fun s => s.regs t 0) = some (some value) := by
  rewrite [hr]
  change some (final.regs t 0) = some (some value)
  rewrite [hv]
  rfl
def prefixOne : Shape := ⟨1,by decide,by decide⟩
def wordInput : Nat → Nat → List Nat := fun _ offset => [offset]
def wordOps : Ops (List Nat) where
  literal := fun n d => if n = -1 ∧ d = 4294967296 then [3] else [4]
  add := fun a b => a ++ b
  sub := fun a b => a ++ b
  mul := fun a b => a ++ b
  max := fun a b => a ++ [1] ++ b
  div := fun a b => a ++ b
  exp := id
  tanh := id
  rsqrt := id
  fromHalf := fun a => 2 :: a
  toHalf := id
'''
    for tid in (0, 81):
        text += f'''theorem source_maximum_word_{tid} :
    threadMaximum wordOps wordInput 0 {tid} = {golden_word(tid)} := by decide
theorem source_prefix_word_{tid} :
    (sourceLane prefixOne false wordOps {tid} sourceFuel.lane
      (sourceInitial prefixOne wordInput (fun _ => none))).map (fun s => s.regs {tid} 0) =
      some (some {golden_word(tid)}) := by
  have run := source_prefix_initial_run prefixOne false wordOps wordInput (fun _ => none) {tid} (by decide)
  have value := source_prefix_initial_value prefixOne wordOps wordInput (fun _ => none) {tid}
  have mapped := source_register_of_run _ _ {tid} _ run value
  exact mapped.trans (congrArg (fun value : List Nat => some (some value)) source_maximum_word_{tid})
'''
    for name in ("source_lane_data", "source_initial_data", "source_prefix_initial_run",
                 "source_prefix_initial_pc", "source_prefix_initial_value", "source_prefix_initial_frames",
                 "source_prefix_initial_inputs", "source_prefix_initial_rf", "source_prefix_cost", "source_register_of_run",
                 "source_maximum_word_0", "source_maximum_word_81", "source_prefix_word_0", "source_prefix_word_81"):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    changes = {
        "changed-infinity-seed": ("maxval = -INFINITY", "maxval = 0.0f"),
        "changed-max-clamp": ("max_col = 50256", "max_col = 50255"),
        "omitted-inner-component": ("while (max_u < 8)", "while (max_u < 7)"),
        "changed-outer-stride": ("max_i = max_i + 8192", "max_i = max_i + 4096"),
        "swapped-max-operands": ("fmaxf(maxval, max_input)", "fmaxf(max_input, maxval)"),
        "changed-first-shuffle": ("__shfl_down(maxval, 16, 32)", "__shfl_xor(maxval, 16, 32)"),
        "changed-later-output": ("norm_value / total_sum", "norm_value"),
    }
    result = {}
    for name, (before, after) in changes.items():
        changed = original.replace(before, after, 1)
        require(changed != original, "Vacuous source mutation: " + name)
        result[name] = statement(changed, fixed, task)
    result["wrong-source-lane-fuel"] = positive.replace(
        "def sourceFuel : Fuel := ⟨4096,8,5,1⟩", "def sourceFuel : Fuel := ⟨4095,8,5,1⟩", 1) + "\nexample : sourceFuel.lane = 4096 := by decide\n"
    result["wrong-source-private-layout"] = positive.replace(
        "def sourceLocals : List Nat := [8, 8]", "def sourceLocals : List Nat := [8, 7]", 1) + "\nexample : sourceLocals = [8,8] := by decide\n"
    common = "import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-prefix-pc"] = common + '''example :
    (maxPrefixState wordOps wordInput 0 (sourceInitial prefixOne wordInput (fun _ => none))).pc 0 = 19 := by
  rewrite [source_prefix_initial_pc]
  decide
'''
    result["wrong-prefix-trace-length"] = common + '''example :
    (maxPrefixState wordOps wordInput 0 (sourceInitial prefixOne wordInput (fun _ => none))).trace.length = 55 := by
  rewrite [(source_prefix_initial_frames prefixOne wordOps wordInput (fun _ => none) 0).2.2]
  decide
'''
    result["insufficient-prefix-fuel"] = common + '''example :
    (sourceLane prefixOne false wordOps 0 1 (sourceInitial prefixOne wordInput (fun _ => none))).isSome = true := by
  change false = true
  decide
'''
    for name, options in {
        "missing-half-conversion": {"cast": False},
        "wrong-clamped-value": {"clamp": 50255},
        "omitted-final-round": {"count": 48},
        "reversed-input-order": {"reverse": True},
        "wrong-initial-value": {"seed": 4},
    }.items():
        result[name] = common + f"example : threadMaximum wordOps wordInput 0 0 = {golden_word(0, **options)} := by\n  rewrite [source_maximum_word_0]\n  decide\n"
    result["wrong-exact-instruction-count"] = common + "example : maxPrefixCost 0 = 496 := by\n  rewrite [max_prefix_cost_exact 0 (by decide)]\n  decide\n"
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
    for module in sorted(closure):
        path = module.replace(".", "/") + ".lean"
        destination = project / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean" / path, destination)
    (project / "lakefile.toml").write_text('name = "native_softmax_max_prefix"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_prefix import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete maximum-prefix statement match.")
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
    require({"source_prefix_initial_run", "source_prefix_initial_value", "source_prefix_initial_inputs",
             "source_prefix_initial_rf", "source_prefix_initial_frames", "source_prefix_word_0",
             "source_prefix_word_81", "LarkNativeSoftmax.initial_max_prefix_run"} <= audits.keys(), "Prefix audits absent")
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
        "Both full source variants execute their scalar maximum prefix to PC20 with the original fuel.\n"
        "The actual56-access prefix reads input only, preserves memory and is race-free, for arbitrary inputs/operations.\n"
        "Logical reductions, later passes, the complete launch and reference bridge remain open. Source certificates0.\n")
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
        "schema": 1, "status": "native-softmax-source-bound-maximum-prefix-checked", "stage": "max-prefix",
        "rows": {"min": 1, "max": native.MAX_ROWS}, "local_lean_modules": len(closure),
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_sha256": {"original": hashlib.sha256(original.encode()).hexdigest(), "fixed": hashlib.sha256(fixed.encode()).hexdigest()},
        "axiom_audits": audits, "false_lean_claims_rejected": len(mutations), "checks": checks,
        "actual_maximum_prefix_execution_proved": True, "starts_at_actual_initializer": True,
        "endpoint_pc": 20, "accesses_per_lane": 56, "all_prefix_accesses_are_input_reads_proved": True,
        "source_ordered_maximum_value_proved": True, "all_memory_and_epochs_preserved_proved": True,
        "original_lane_fuel": 4096, "exact_instruction_counts": {"tid0_through80": 497, "tid81_through1023": 498},
        "prefix_race_freedom_proved": True, "race_freedom_assumed": False,
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
