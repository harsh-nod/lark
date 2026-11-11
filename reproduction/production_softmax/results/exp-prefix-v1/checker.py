"""Fresh source-bound native softmax scalar exponentiation/sum prefix.

After the proved maximum pass, each selected lane executes all seven scalar
rounds and parks at PC70. Collective sum reduction and later phases stay open;
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
from reproduction.production_softmax import check_maximum as maximum  # noqa: E402
from reproduction.production_softmax.prepare import source  # noqa: E402

base, prefix, native = maximum.base, maximum.prefix, maximum.native
HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSoftmaxExpPrefixCounts"
sha, require = maximum.sha, maximum.require


WORD_TIDS = (0, 80, 81, 1023)
WORD_MAXIMUM = 150772
WORD_MODEL = {"max":"right projection", "add":"7*a+b", "sub":"2*a+b", "exp":"5*a+3",
              "fromHalf":"3*a+1", "toHalf":"7*a+1"}


def golden_word(tid, *, reverse_sub=False, rounded_sum=False):
    result, count = 0, 0
    for iteration in range(7):
        for component in range(8):
            col = tid + (iteration*8+component)*1024
            if col < 50257:
                value = 3*(col+1)+1
                sub = 2*WORD_MAXIMUM+value if reverse_sub else 2*value+WORD_MAXIMUM
                exponential = 5*sub+3
                result = 7*result + (7*exponential+1 if rounded_sum else exponential)
                count += 1
    first = 5*(2*(3*(tid+1)+1)+WORD_MAXIMUM)+3
    return {"valid":count, "sum":result, "first_unrounded":first, "first_output":7*first+1}


EXP_PRINCIPAL = {
    "source_exp_initial_entry", "source_exp_initial_run", "source_exp_initial_pc", "source_exp_initial_epoch",
    "source_exp_initial_sum", "source_exp_initial_outputs", "source_exp_output_value", "source_exp_output_run",
    "source_exp_initial_good", "source_exp_initial_rf", "source_exp_initial_native",
    "source_exp_initial_trace_length", "source_exp_initial_trace_total", "source_exp_sum_run",
    "source_exp_register_of_run", "source_exp_trace_total_of_start", "source_exp_word_sum_run", "source_exp_word_output_run",
    "LarkNativeSoftmax.exp_prefix_run", "LarkNativeSoftmax.exp_prefix_outputs", "LarkNativeSoftmax.exp_prefix_cost_exact",
    "LarkNativeSoftmax.exp_prefix_trace_exact", "LarkNativeSoftmax.initial_exp_prefix_run", "LarkNativeSoftmax.initial_exp_prefix_race_free",
}
PRINCIPAL = maximum.PRINCIPAL | EXP_PRINCIPAL


def statement(original, fixed, task):
    text = maximum.statement(original, fixed, task).replace(
        "import Lark.NativeSoftmaxMaximum\n",
        "import Lark.NativeSoftmaxMaximum\nimport Lark.NativeSoftmaxExpPrefixCounts\n", 1)
    text += '''
def sourceExpState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) : State α :=
  expPrefixState ops input row tid (sourceMaximumState p ops input outside row)
theorem source_exp_initial_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ExpLaneEntry p ops input row tid (sourceMaximumState p ops input outside row) :=
  exp_lane_entry_of_maximum p ops input row tid _ (source_maximum_initial_ready p ops input outside row hr) ht
theorem source_exp_initial_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    sourceLane p guarded ops (row*1024+tid) sourceFuel.lane (sourceMaximumState p ops input outside row) =
      some (sourceExpState p ops input outside row tid) := by
  rewrite [source_lane_data,(source_interface_data p).2.2]
  exact exp_prefix_run p guarded ops input row tid _ (source_exp_initial_entry p ops input outside row tid hr ht)
theorem source_exp_initial_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) :
    (sourceExpState p ops input outside row tid).pc (row*1024+tid)=70 :=
  exp_prefix_pc ops input row tid (sourceMaximumState p ops input outside row)
theorem source_exp_initial_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceExpState p ops input outside row tid).epochs (row*1024+tid)).block=2 :=
  (congrArg (fun epochs => (epochs (row*1024+tid)).block)
    (exp_prefix_epochs ops input row tid (sourceMaximumState p ops input outside row))).trans
    (source_maximum_initial_epoch p ops input outside row tid hr ht)
theorem source_exp_initial_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    (sourceExpState p ops input outside row tid).regs (row*1024+tid) 6=some (threadExpSum ops input row tid) :=
  exp_prefix_sum p ops input row tid _ (source_exp_initial_entry p ops input outside row tid hr ht)
theorem source_exp_initial_outputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (ht : tid<1024) :
    ExpPastOutputs ops input (rowMaximum ops input row) row tid 7 (sourceExpState p ops input outside row tid) :=
  exp_prefix_outputs ops input row tid (sourceMaximumState p ops input outside row) ht
theorem source_exp_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid iteration component : Nat) (ht : tid<1024)
    (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257) :
    (sourceExpState p ops input outside row tid).memory (globalCell 0 (address row (column tid iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row tid iteration component)) :=
  source_exp_initial_outputs p ops input outside row tid ht iteration hi component hc hcol
theorem source_exp_output_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid iteration component : Nat) (hr : row<p.rows) (ht : tid<1024)
    (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257) :
    (sourceLane p guarded ops (row*1024+tid) sourceFuel.lane (sourceMaximumState p ops input outside row)).map
      (fun s => s.memory (globalCell 0 (address row (column tid iteration component))))=
        some (some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row tid iteration component))) :=
  source_memory_of_run _ (sourceExpState p ops input outside row tid) _ _
    (source_exp_initial_run p guarded ops input outside row tid hr ht)
    (source_exp_output_value p ops input outside row tid iteration component ht hi hc hcol)
theorem source_exp_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ∀ a ∈ (sourceExpState p ops input outside row tid).trace, Good a :=
  exp_prefix_good p ops input row tid _ (source_exp_initial_entry p ops input outside row tid hr ht)
theorem source_exp_initial_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    raceFree (sourceGeometry p) (sourceExpState p ops input outside row tid).trace=true := by
  rewrite [(source_interface_data p).2.1]
  exact exp_prefix_race_free p ops input row tid _ (source_exp_initial_entry p ops input outside row tid hr ht)
theorem source_exp_initial_native (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    MaxNativeIndices (row*1024+tid) (sourceExpState p ops input outside row tid) :=
  exp_prefix_native ops input row tid (sourceMaximumState p ops input outside row)
    ((source_maximum_initial_ready p ops input outside row hr).indices tid ht)
theorem source_exp_initial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (ht : tid<1024) :
    (sourceExpState p ops input outside row tid).trace.length=
      (sourceMaximumState p ops input outside row).trace.length+(if tid<81 then 213 else 211) :=
  exp_prefix_trace_exact ops input row tid (sourceMaximumState p ops input outside row) ht
theorem source_exp_trace_total_of_start (start final : State α) (n k : Nat)
    (hstart : start.trace.length=n) (hfinal : final.trace.length=start.trace.length+k) :
    final.trace.length=n+k := by
  rewrite [hstart] at hfinal
  exact hfinal
theorem source_exp_initial_trace_total (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (ht : tid<1024) :
    (sourceExpState p ops input outside row tid).trace.length=57409+(if tid<81 then 213 else 211) :=
  source_exp_trace_total_of_start (sourceMaximumState p ops input outside row)
    (sourceExpState p ops input outside row tid) 57409 (if tid<81 then 213 else 211)
    (source_maximum_initial_trace_length p ops input outside row) (source_exp_initial_trace_length p ops input outside row tid ht)
theorem source_exp_register_of_run (run : Option (State α)) (final : State α) (t r : Nat) (value : α)
    (hr : run=some final) (hv : final.regs t r=some value) :
    run.map (fun s => s.regs t r)=some (some value) := by
  rewrite [hr]
  change some (final.regs t r)=some (some value)
  rewrite [hv]
  rfl
theorem source_exp_sum_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    (sourceLane p guarded ops (row*1024+tid) sourceFuel.lane (sourceMaximumState p ops input outside row)).map
      (fun s => s.regs (row*1024+tid) 6)=some (some (threadExpSum ops input row tid)) :=
  source_exp_register_of_run _ (sourceExpState p ops input outside row tid) (row*1024+tid) 6 _
    (source_exp_initial_run p guarded ops input outside row tid hr ht)
    (source_exp_initial_sum p ops input outside row tid hr ht)
def expWordOps : Ops Nat where
  literal := fun _ _ => 0
  add := fun a b => 7*a+b
  sub := fun a b => 2*a+b
  mul := Nat.mul
  max := fun _ b => b
  div := Nat.div
  exp := fun a => 5*a+3
  tanh := id
  rsqrt := id
  fromHalf := fun a => 3*a+1
  toHalf := fun a => 7*a+1
def expWordInput : Nat → Nat → Nat := fun _ offset => offset+1
def expWordOne : Shape := ⟨1,by decide,by decide⟩
theorem exp_word_maximum : rowMaximum expWordOps expWordInput 0=150772 := by decide
'''
    for tid in WORD_TIDS:
        value = golden_word(tid)
        text += f'''theorem exp_word_sum_{tid} : threadExpSum expWordOps expWordInput 0 {tid}={value["sum"]} := by
  simp only [threadExpSum,exp_word_maximum]
  decide
theorem exp_word_output_{tid} :
    expWordOps.toHalf (expComponentValue expWordOps expWordInput (rowMaximum expWordOps expWordInput 0) 0 {tid} 0 0)={value["first_output"]} := by
  simp only [exp_word_maximum]
  decide
'''
    text += '''theorem source_exp_word_sum_run (guarded : Bool) (tid n : Nat) (ht : tid<1024)
    (hsum : threadExpSum expWordOps expWordInput 0 tid=n) :
    (sourceLane expWordOne guarded expWordOps (0*1024+tid) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.regs (0*1024+tid) 6)=some (some n) :=
  (source_exp_sum_run expWordOne guarded expWordOps expWordInput (fun _ => none) 0 tid (by decide) ht).trans
    (congrArg (fun value : Nat => some (some value)) hsum)
theorem source_exp_word_output_run (guarded : Bool) (tid n : Nat) (ht : tid<1024)
    (hout : expWordOps.toHalf (expComponentValue expWordOps expWordInput (rowMaximum expWordOps expWordInput 0) 0 tid 0 0)=n) :
    (sourceLane expWordOne guarded expWordOps (0*1024+tid) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.memory (globalCell 0 (address 0 (column tid 0 0))))=some (some n) :=
  (source_exp_output_run expWordOne guarded expWordOps expWordInput (fun _ => none) 0 tid 0 0
    (by decide) ht (by decide) (by decide) (by unfold column; omega)).trans
    (congrArg (fun value : Nat => some (some value)) hout)
'''
    for tid in WORD_TIDS:
        value = golden_word(tid)
        text += f'''theorem source_exp_word_sum_{tid} (guarded : Bool) :
    (sourceLane expWordOne guarded expWordOps (0*1024+{tid}) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.regs (0*1024+{tid}) 6)=some (some {value["sum"]}) :=
  source_exp_word_sum_run guarded {tid} {value["sum"]} (by decide) exp_word_sum_{tid}
theorem source_exp_word_output_{tid} (guarded : Bool) :
    (sourceLane expWordOne guarded expWordOps (0*1024+{tid}) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.memory (globalCell 0 (address 0 (column {tid} 0 0))))=some (some {value["first_output"]}) :=
  source_exp_word_output_run guarded {tid} {value["first_output"]} (by decide) exp_word_output_{tid}
'''
    names = EXP_PRINCIPAL | {"exp_word_maximum"}
    for tid in WORD_TIDS:
        names |= {f"exp_word_sum_{tid}", f"exp_word_output_{tid}", f"source_exp_word_sum_{tid}", f"source_exp_word_output_{tid}"}
    for name in sorted(names):
        text += "#print axioms " + name + "\n"
    return text


def controls(original, fixed, task, positive):
    result = maximum.controls(original, fixed, task, maximum.statement(original, fixed, task))
    for name, before, after in (
        ("exp-input-round-trip", "exp_regs[exp_load_u] = __half2float(inp[exp_load_address]);", "exp_regs[exp_load_u] = __half2float(__float2half(__half2float(inp[exp_load_address])));"),
        ("exp-private-bank-changed", "exp_regs[exp_load_u] =", "norm_regs[exp_load_u] ="),
        ("exp-subtraction-reversed", "expf(exp_input - offset)", "expf(offset - exp_input)"),
        ("exp-output-from-input", "out[exp_store_address] = __float2half(exp_value);", "out[exp_store_address] = __float2half(exp_input);"),
        ("exp-guard-changed", "if (exp_store_col < 50257)", "if (exp_store_col <= 50257)"),
        ("exp-sum-from-rounded-output", "sumval = sumval + exp_value;", "sumval = sumval + __half2float(out[exp_store_address]);"),
        ("exp-stride-changed", "exp_i = exp_i + 8192", "exp_i = exp_i + 4096"),
        ("exp-clamp-changed", "exp_load_col = 50256", "exp_load_col = 50255"),
        ("exp-exit-temp-changed", "float sum_other = 0.0f", "float sum_other = 1.0f"),
    ):
        changed = original.replace(before, after, 1)
        require(changed != original, "Vacuous exp source control: " + name)
        result[name] = maximum.block.statement(changed, fixed, task)
    common = "import Main\nopen LarkNonlinear LarkNativeSoftmax\n"
    result["wrong-exp-endpoint"] = common + '''example :
    (sourceExpState prefixOne wordOps wordInput (fun _ => none) 0 0).pc (0*1024+0)=69 := by
  rewrite [source_exp_initial_pc]
  decide
'''
    result["invented-exp-barrier"] = common + '''example :
    ((sourceExpState prefixOne wordOps wordInput (fun _ => none) 0 0).epochs (0*1024+0)).block=3 := by
  rewrite [source_exp_initial_epoch prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide) (by decide)]
  decide
'''
    result["wrong-exp-access-count"] = common + '''example :
    (sourceExpState prefixOne wordOps wordInput (fun _ => none) 0 0).trace.length=57620 := by
  rewrite [source_exp_initial_trace_total prefixOne wordOps wordInput (fun _ => none) 0 0 (by decide)]
  change 57622=57620
  decide
'''
    for name, claim, theorem in (
        ("wrong-exp-early-cost", "expPrefixCost 0=978", "exp_prefix_cost_exact 0 (by decide)"),
        ("wrong-exp-tail-cost", "expPrefixCost 81=982", "exp_prefix_cost_exact 81 (by decide)"),
        ("wrong-exp-valid-stores", "expRoundsCount 0 0 7=49", "exp_rounds_count_exact 0 (by decide)"),
    ):
        result[name] = common + f"example : {claim} := by\n  rewrite [{theorem}]\n  decide\n"
    for name, tid, wrong in (
        ("exp-rounded-sum-value", 0, golden_word(0, rounded_sum=True)["sum"]),
        ("exp-reversed-sub-value", 0, golden_word(0, reverse_sub=True)["sum"]),
        ("wrong-exp-edge-value", 81, golden_word(80)["sum"]),
    ):
        require(wrong != golden_word(tid)["sum"], "Vacuous exp value control")
        result[name] = common + f'''example :
    (sourceLane expWordOne true expWordOps (0*1024+{tid}) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.regs (0*1024+{tid}) 6)=some (some {wrong}) := by
  rewrite [source_exp_word_sum_{tid}]
  decide
'''
    result["exp-unconverted-output-value"] = common + f'''example :
    (sourceLane expWordOne true expWordOps (0*1024+0) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).map
        (fun s => s.memory (globalCell 0 (address 0 (column 0 0 0))))=some (some {golden_word(0)["first_unrounded"]}) := by
  rewrite [source_exp_word_output_0]
  decide
'''
    result["invented-exp-none"] = common + '''example :
    (sourceLane expWordOne false expWordOps (0*1024+0) sourceFuel.lane
      (sourceMaximumState expWordOne expWordOps expWordInput (fun _ => none) 0)).isSome=false := by
  rewrite [source_exp_initial_run expWordOne false expWordOps expWordInput (fun _ => none) 0 0 (by decide) (by decide)]
  change true=false
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
    (project / "lakefile.toml").write_text('name = "native_softmax_exp_prefix"\nversion = "0.1.0"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Lark"\n[[lean_lib]]\nname = "Main"\n')
    shutil.copyfile(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    positive = statement(original, fixed, task)
    (project / "Main.lean").write_text(positive)
    frozen = project / "reproduction/production_softmax"
    frozen.mkdir(parents=True)
    for name in ("prepare.py", "check_program.py", "check_prefix.py", "check_first_wave.py", "check_first_block.py", "check_maximum.py", "check_exp_prefix.py", "trace_full.py", "provenance.json", "rewrites.json"):
        shutil.copyfile(HERE / name, frozen / name)
    shutil.copytree(HERE / "cases", frozen / "cases")
    shutil.copytree(HERE / "upstream", frozen / "upstream")
    shutil.copyfile(ROOT / "reproduction/__init__.py", project / "reproduction/__init__.py")
    (project / "lark_kernels").mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, project / "lark_kernels" / path.name)
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    (project / "validate_source.py").write_text('''from pathlib import Path
from reproduction.production_softmax.check_exp_prefix import HERE, statement, native
from reproduction.production_softmax.prepare import source
root=Path(__file__).resolve().parent
original=(HERE/"cases/native_race/kernel.hip").read_text()
fixed=(HERE/"cases/native_fixed/kernel.hip").read_text()
assert original==source(False) and fixed==source(True)
task=native.parse_task((HERE/"cases/native_race/task.json").read_text())
assert statement(original,fixed,task)==(root/"Main.lean").read_text()
print("Both full source/reader/IR/interface bindings and the complete scalar exponentiation/sum-prefix and inherited maximum-pass statement match.")
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
    execute("fresh-exp-library-build", ["lake", "build", TARGET], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    require(PRINCIPAL <= audits.keys(), "Exp-prefix audits absent")
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
        "This is an individual-lane prefix, not a collective sum reduction or complete softmax launch.\n"
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
        "schema": 1, "status": "native-softmax-source-bound-exp-prefix-checked", "stage": "exp-prefix",
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
        "actual_exp_wave_fold_execution_proved": False, "actual_exp_block_phase_execution_proved": False,
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
