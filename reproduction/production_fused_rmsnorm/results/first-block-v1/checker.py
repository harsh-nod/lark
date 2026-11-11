"""Fresh source-bound native in-place execution-prefix proofs; no GPU/model calls.

This proves the actual 210-instruction prefix through both in-place rounds,
ending at PC23 before any shuffle. The first-wave stage additionally proves all
64 native lanes through five logical32 reductions/two partial stores to PC35.
The first-block stage composes all sixteen waves and the actual barrier resume
to PC36/epoch1, retaining every rounded residual and unrounded shared value.
Whole-launch and canonical-real source correctness remain open. Existing frozen
component/GPU/prefix packets are unchanged.
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
from lark_kernels import native_fused_rmsnorm as native  # noqa: E402
from reproduction.production_fused_rmsnorm import check_program as component  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_16384"
TARGET = "Lark.NativeFusedRmsNormPrefix"
TARGETS = {"lane": TARGET, "first-wave": "Lark.NativeFusedRmsNormFirstWave",
           "first-block": "Lark.NativeFusedRmsNormBarrier"}
SOURCE_SHA256 = "c297c1842c1a4d2d9be2265aa0d03da759dda22f555947e3483eccb486e5f59e"
PRINCIPAL = (
    "source_binding", "source_prefix_all_shapes", "source_prefix_values",
    "source_prefix_good", "source_prefix_race_free", "source_prefix_access_count",
    "LarkNativeFusedRmsNorm.component_cycle", "LarkNativeFusedRmsNorm.components_eq",
    "LarkNativeFusedRmsNorm.round_eq", "LarkNativeFusedRmsNorm.prefix_eq",
    "LarkNativeFusedRmsNorm.initial_prefix_run", "LarkNativeFusedRmsNorm.initial_prefix_values",
    "LarkNativeFusedRmsNorm.initial_prefix_good", "LarkNativeFusedRmsNorm.initial_prefix_race_free",
)
WAVE_PRINCIPAL = (
    "source_first_wave_run", "source_first_wave_partials", "source_first_wave_cells",
    "source_first_wave_good", "source_first_wave_race_free",
    "LarkNativeFusedRmsNorm.owns_unique", "LarkNativeFusedRmsNorm.prefix_fold_run",
    "LarkNativeFusedRmsNorm.xor_peer_partition", "LarkNativeFusedRmsNorm.native_first_four",
    "LarkNativeFusedRmsNorm.last_fold_value", "LarkNativeFusedRmsNorm.first_wave_run",
    "LarkNativeFusedRmsNorm.first_wave_initial", "LarkNativeFusedRmsNorm.first_wave_initial_race_free",
)
BLOCK_PRINCIPAL = (
    "source_first_block_run", "source_first_block_values", "source_first_block_partials",
    "source_first_block_participants", "source_first_block_cut", "source_first_barrier_resume",
    "source_first_barrier_state", "source_first_barrier_race_free",
    "LarkNativeFusedRmsNorm.first_wave_memory_frame", "LarkNativeFusedRmsNorm.wave_fold_run",
    "LarkNativeFusedRmsNorm.wave_fold_member", "LarkNativeFusedRmsNorm.wave_fold_partial",
    "LarkNativeFusedRmsNorm.first_block_cells", "LarkNativeFusedRmsNorm.first_block_cut",
    "LarkNativeFusedRmsNorm.block_first_eq", "LarkNativeFusedRmsNorm.mid_ready",
    "LarkNativeFusedRmsNorm.initial_first_barrier",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def statement(source, contract, stage="lane"):
    identity = component.statement(source, contract).replace(
        "import Lark.NativeFusedRmsNormAddress", f"import {TARGETS[stage]}", 1)
    text = identity + """
theorem source_prefix_all_shapes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) sourceProgram t sourceFuel.lane
      (initial p input outside) = some (prefixState ops input t (initial p input outside)) := by
  simpa only [source_binding.1, source_binding.2.2.2.2.1] using initial_prefix_run p ops input outside t ht
theorem source_prefix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    (prefixState ops input t (initial p input outside)).regs t 0 =
      some (threadSum ops input (t / 1024) (t % 1024)) ∧
    Pending input (t / 1024) (t % 1024) 16 (prefixState ops input t (initial p input outside)) ∧
    Completed ops input (t / 1024) (t % 1024) t 16 (prefixState ops input t (initial p input outside)) :=
  initial_prefix_values p ops input outside t ht
theorem source_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    ∀ a ∈ (prefixState ops input t (initial p input outside)).trace, Good a :=
  initial_prefix_good p ops input outside t ht
theorem source_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    raceFree (geometry p) (prefixState ops input t (initial p input outside)).trace = true :=
  initial_prefix_race_free p ops input outside t ht
theorem source_prefix_access_count (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (prefixState ops input t (initial p input outside)).trace.length = 64 :=
  initial_prefix_trace_length p ops input outside t
#print axioms source_prefix_all_shapes
#print axioms source_prefix_values
#print axioms source_prefix_good
#print axioms source_prefix_race_free
#print axioms source_prefix_access_count
"""
    if stage in {"first-wave", "first-block"}:
        text += """
theorem source_first_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) sourceFuel sourceProgram
      (warpThreads (geometry p) row warp) sourceFuel.warp (initial p input outside) =
      some (firstWave p ops input row warp (initial p input outside)) := by
  simpa only [source_binding.1, source_binding.2.2.2.2.1] using
    first_wave_initial p ops input outside row warp hr hw
theorem source_first_wave_partials (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp half : Nat) (hw : warp < 16) (hh : half < 2) :
    (firstWave p ops input row warp (initial p input outside)).memory ⟨.shared,row,0,warp*2+half⟩ =
      some (waveValues ops input row warp 5 (half*32)) :=
  first_wave_partial p ops input row warp half _ hw hh
theorem source_first_wave_cells (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16)
    (t : Nat) (ht : t ∈ cohortThreads row warp 64) :
    Pending input (t/1024) (t%1024) 16 (firstWave p ops input row warp (initial p input outside)) ∧
    Completed ops input (t/1024) (t%1024) t 16 (firstWave p ops input row warp (initial p input outside)) :=
  first_wave_cells p ops input row warp _ hr hw
    (initial_pending_lanes p input outside _ (cohort_bound p row warp 64 hr hw (by decide)))
    (by intro a ha; cases ha) t ht
theorem source_first_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    ∀ a ∈ (firstWave p ops input row warp (initial p input outside)).trace, Good a :=
  first_wave_initial_good p ops input outside row warp hr hw
theorem source_first_wave_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    raceFree (geometry p) (firstWave p ops input row warp (initial p input outside)).trace = true :=
  first_wave_initial_race_free p ops input outside row warp hr hw
#print axioms source_first_wave_run
#print axioms source_first_wave_partials
#print axioms source_first_wave_cells
#print axioms source_first_wave_good
#print axioms source_first_wave_race_free
"""
    if stage == "first-block":
        text += """
theorem source_first_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    (List.range 16).foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p)
      sourceFuel sourceProgram (warpThreads (geometry p) row w) sourceFuel.warp s)
      (initial p input outside) = some (firstBlock p ops input row (initial p input outside)) := by
  simpa only [source_binding.1, source_binding.2.2.2.2.1] using first_block_initial_run p ops input outside row hr
theorem source_first_block_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row col : Nat) (hr : row < p.rows) (hc : col < 16384) :
    (firstBlock p ops input row (initial p input outside)).memory (globalCell 1 (address row col)) =
      some (ops.toHalf (rowAdded ops input row col)) ∧
    (firstBlock p ops input row (initial p input outside)).memory ⟨.shared,row,1,col⟩ =
      some (rowAdded ops input row col) :=
  first_block_cells p ops input row col _ (initial_block_entry p input outside row hr) hc
theorem source_first_block_partials (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row k : Nat) (hk : k < 32) :
    (firstBlock p ops input row (initial p input outside)).memory ⟨.shared,row,0,k⟩ =
      some (blockPartial ops input row k) := first_block_partial p ops input row k _ hk
theorem source_first_block_participants (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    FirstDone ops input (row*1024+tid) (firstBlock p ops input row (initial p input outside)) :=
  first_block_member p ops input row tid _ (initial_block_entry p input outside row hr) ht
theorem source_first_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    LarkCollective.converged sourceProgram (blockThreads (geometry p) row)
      (firstBlock p ops input row (initial p input outside)) = some .block := by
  simpa only [source_binding.1] using first_block_cut p ops input row _ (initial_block_entry p input outside row hr)
theorem source_first_barrier_resume (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) sourceFuel sourceProgram row sourceFuel.block
      (initial p input outside) =
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) sourceFuel sourceProgram row 2
      (midState p ops input row (initial p input outside)) := by
  simpa only [source_binding.1, source_binding.2.2.2.2.1] using initial_first_barrier p ops input outside row hr
theorem source_first_barrier_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    MidReady p ops input row (midState p ops input row (initial p input outside)) :=
  initial_mid_ready p ops input outside row hr
theorem source_first_barrier_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (geometry p) (midState p ops input row (initial p input outside)).trace = true :=
  initial_mid_race_free p ops input outside row hr
#print axioms source_first_block_run
#print axioms source_first_block_values
#print axioms source_first_block_partials
#print axioms source_first_block_participants
#print axioms source_first_block_cut
#print axioms source_first_barrier_resume
#print axioms source_first_barrier_state
#print axioms source_first_barrier_race_free
"""
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stage", choices=tuple(TARGETS), default="lane")
    args = parser.parse_args()
    wave_stage = args.stage != "lane"
    block_stage = args.stage == "first-block"
    target = TARGETS[args.stage]
    out = args.output.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Fresh standalone output must be outside a Git checkout")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    own = {}
    component.modules(target, own)
    for name, text in own.items():
        dest = project / (name.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
    (project / "lakefile.toml").write_text('''name = "fused_scalar_prefix"
version = "0.1.0"
defaultTargets = ["Main"]
[[lean_lib]]
name = "Lark"
[[lean_lib]]
name = "Main"
''')
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    source = (CASE / "kernel.hip").read_text()
    if sha(CASE / "kernel.hip") != SOURCE_SHA256:
        raise ValueError("Pinned source changed")
    contract = native.parse_task((CASE / "task.json").read_text())
    native.check_reference((CASE / "reference.py").read_text())
    (project / "Main.lean").write_text(statement(source, contract, args.stage))
    reader_dir = project / "lark_kernels"
    reader_dir.mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, reader_dir / path.name)
    source_dir = project / "native-source"
    source_dir.mkdir()
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(CASE / name, source_dir / name)
    shutil.copyfile(HERE / "provenance.json", source_dir / "provenance.json")
    licenses = project / "licenses"
    licenses.mkdir()
    for name in ("FLASHINFER_LICENSE", "SGLANG_LICENSE"):
        shutil.copyfile(HERE / "upstream" / name, licenses / name)
    remaining = ("Composition across native waves, block-barrier resume, second reduction,\n"
                 "output normalization, halt, grid, canonical-real/IEEE equivalence\n"
                 "and original-paper results remain open.\n") if wave_stage else (
        "Logical32 shuffles, barriers, output normalization, halt, scheduling,\n"
        "canonical-real/IEEE equivalence and original-paper results remain open.\n")
    if block_stage:
        remaining = ("The second reduction, normalization, second barrier, halt/grid,\n"
                     "canonical-real/IEEE equivalence and original-paper results remain open.\n")
    title = ("Native fused add RMSNorm first block phase and barrier resume, PC36/epoch1.\n" if block_stage else
             "Native fused add RMSNorm first-wave proof, ending at PC35.\n" if wave_stage else
             "Per-lane native fused add RMSNorm scalar-prefix proof, ending at PC23.\n")
    (project / "README.md").write_text(
        title +
        "Requires Python 3 and Lean 4.19.0; no Git, GPUs or models.\n"
        "Replay the frozen reader: python3 validate_source.py\n"
        "Rebuild from source: lake build\n"
        "Positive concrete witnesses: lake env lean Witnesses.lean\n"
        "Every other top-level .lean file except Main.lean is a control that must\n"
        "fail with 'is false' at its assertion. No .lake objects are archived.\n"
        "All inputs/operations/outside memory and valid lanes/rows1..255 are\n"
        "quantified by the prefix theorem. This is not a full kernel certificate.\n" + remaining)
    # The archived replay derives the translated IR again from frozen source,
    # without importing the live checkout or depending on Git.
    (project / "validate_source.py").write_text('''from pathlib import Path
import hashlib
from lark_kernels import collective, native_fused_rmsnorm as native
from lark_kernels.ir import lean_list
root = Path(__file__).resolve().parent
case = root / "native-source"
assert hashlib.sha256((case / "kernel.hip").read_bytes()).hexdigest() == "c297c1842c1a4d2d9be2265aa0d03da759dda22f555947e3483eccb486e5f59e"
contract = native.parse_task((case / "task.json").read_text())
native.check_reference((case / "reference.py").read_text())
translation = native.translate((case / "kernel.hip").read_text(), contract)
main = (root / "Main.lean").read_text()
body = main.split("def sourceProgram : List LarkCollective.Instr := [\\n", 1)[1].split("\\n]\\n", 1)[0]
assert body == ",\\n".join(collective.emit(i) for i in translation.program)
task = contract.task
assert f"def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩" in main
globals_text = lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)
assert f"def sourceGlobal : List Buffer := {globals_text}" in main
assert f"def sourceShared : List Nat := {[n for _, n in translation.shared]}" in main
assert f"def sourceMutable : List Nat := {list(contract.inout)}" in main
assert f"def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩" in main
assert f"def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩" in main
print("Frozen source/reader/IR/interface/fuel binding replay passed.")
''')
    checks = []

    def execute(name, command, expected=True):
        start = time.monotonic()
        run = subprocess.run(command, cwd=project, capture_output=True, text=True,
                             timeout=600 if block_stage and name == "fresh-build" else 300)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "sorryAx" not in log and "error:" not in log
        if accepted != expected:
            raise ValueError(name + ": unexpected acceptance\n" + log)
        if not expected and ("error:" not in log or "is false" not in log):
            raise ValueError(name + ": rejection did not reach the false-claim gate\n" + log)
        checks.append({"name": name, "expected_accepted": expected, "accepted": accepted,
                       "exit_code": run.returncode, "seconds": time.monotonic() - start, "timed_out": False})
        return log

    execute("frozen-reader-replay", [sys.executable, "validate_source.py"])
    log = execute("fresh-build", ["lake", "build"])
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    principal = PRINCIPAL + (WAVE_PRINCIPAL if wave_stage else ()) + (BLOCK_PRINCIPAL if block_stage else ())
    if set(principal) - audits.keys():
        raise ValueError("Principal axiom audits absent: " + str(set(principal) - audits.keys()))
    for name, ax in audits.items():
        if set(x.strip() for x in ax.split(",") if x.strip()) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("Extra axiom in " + name)
    variants = {
        "skipped-second-round": source.replace("while (iteration < 2)", "while (iteration < 1)", 1),
        "wrong-residual-value": source.replace("__float2half(x);", "__float2half(r);", 1),
        "rounded-shared-value": source.replace("unrounded[column] = x;", "unrounded[column] = __half2float(residual[address]);", 1),
        "wrong-component-stride": source.replace("component = component + 1;", "component = component + 2;", 1),
    }
    if wave_stage:
        variants.update({
            "cross-logical-partition-shuffle": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 16, 64)", 1),
            "missing-second-partial-writer": source.replace("if (lane == 0)", "if (t == 0)", 1),
            "aliased-partial-slot": source.replace("partial[warp] = sum", "partial[warp / 2] = sum", 1),
            "changed-xor-stage-order": source.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 1, 32)", 1),
        })
    if block_stage:
        variants.update({
            "missing-first-block-barrier": source.replace("__syncthreads();", "", 1),
            "physical-instead-logical-partial-index": source.replace("int warp = t / 32;", "int warp = t / 64;", 1),
        })
    for name, variant in variants.items():
        if variant == source:
            raise ValueError("No-op source control")
        (project / (name + ".lean")).write_text(statement(variant, contract, args.stage))
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    base = f"""import {target}
open LarkNonlinear LarkNativeFusedRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def p : Shape := ⟨1, by decide, by decide⟩
def ops : Ops Nat := ⟨fun n d => n.toNat / d, (· + ·), (· - ·), (· * ·), Nat.max,
  (· / ·), id, id, id, id, fun x => x + 1000⟩
def values (b i : Nat) : Nat := b * 7 + i + 1
def start : State Nat := initial p values (fun _ => none)
def once : State Nat := componentAfter ops values 0 0 0 0 0 0 start
"""
    claims = {
        "omitted-residual-cast": "once.memory (globalCell 1 0) = some (added ops values 0 0 0 0)",
        "rounded-shared-state": "once.memory (unroundedCell 0 0) = some (ops.toHalf (added ops values 0 0 0 0))",
        "overwritten-unread-residual": "once.memory (globalCell 1 1) = some (ops.toHalf (flatAdded ops values 0 0 1))",
        "rounded-square-accumulation": "once.regs 0 0 = some (ops.mul (ops.toHalf (added ops values 0 0 0 0)) (ops.toHalf (added ops values 0 0 0 0)))",
        "wrong-prefix-endpoint": "(prefixState ops values 0 start).pc 0 = 35",
        "wrong-round-exit": "(endRound 0 0 start).indices 0 4 = some 2",
    }
    # Include positive witnesses so the nonidentity cast controls cannot reject
    # solely because of an invalid concrete setup.
    witnesses = """example : once.memory (globalCell 1 0) = some 1009 := by decide
example : once.memory (unroundedCell 0 0) = some 9 := by decide
example : once.memory (globalCell 1 1) = some 9 := by decide
example : once.regs 0 0 = some 81 := by decide
example : (prefixState ops values 0 start).pc 0 = 23 := by decide
"""
    if wave_stage:
        base += "def orderOps : Ops Nat := { ops with add := fun a b => a * 100 + b }\n"
        base += """instance (t : Nat) (l : Location) : Decidable (PartialWrites t l) :=
  inferInstanceAs (Decidable ((t % 1024) % 32 = 0 ∧ l = partialCell t ((t % 1024) / 32)))
"""
        claims.update({
            "upper-half-crossed-partition": "xorPeer32 32 16 = 16",
            "lower-half-crossed-partition": "xorPeer32 31 16 = 47",
            "second-writer-aliased-first-slot": "PartialWrites 32 (partialCell 0 0)",
            "second-partial-store-omitted": "(firstLastAfter ops 32 2 3 start).memory (partialCell 32 1) = none",
            "second-store-overwrote-first-slot": "(firstLastAfter ops 32 2 3 start).memory (partialCell 0 0) = some 5",
            "swapped-post-shuffle-add": "(addAfter orderOps 0 24 2 3 start).regs 0 0 = some 302",
        })
        witnesses += """example : xorPeer32 32 16 = 48 := by decide
example : xorPeer32 31 16 = 15 := by decide
example : PartialWrites 32 (partialCell 32 1) := by decide
example : (firstLastAfter ops 32 2 3 start).memory (partialCell 32 1) = some 5 := by decide
example : (firstLastAfter ops 32 2 3 start).memory (partialCell 0 0) = none := by decide
example : (addAfter orderOps 0 24 2 3 start).regs 0 0 = some 203 := by decide
"""
    if block_stage:
        base += "def marked : State Nat := { start with trace := [⟨0, globalCell 0 0, false, {}⟩] }\n"
        claims.update({
            "skipped-last-physical-wave": "(warpThreads (geometry p) 0 15).contains 1023 = false",
            "crossed-block-participant": "(blockThreads (geometry p) 0).contains 1024 = true",
            "next-wave-overwrote-prior-partial": "PartialWrites 64 ⟨.shared,0,0,1⟩",
            "unchanged-last-lane-pc-after-resume": "(resume (blockThreads (geometry p) 0) .block start).pc 1023 = 0",
            "spurious-next-row-pc-after-resume": "(resume (blockThreads (geometry p) 0) .block start).pc 1024 = 1",
            "unchanged-last-lane-block-epoch": "((resume (blockThreads (geometry p) 0) .block start).epochs 1023).block = 0",
            "spurious-next-row-block-epoch": "((resume (blockThreads (geometry p) 0) .block start).epochs 1024).block = 1",
            "erased-historical-trace-on-resume": "(resume (blockThreads (geometry p) 0) .block marked).trace.length = 0",
            "rewritten-historical-epoch-on-resume": "((resume (blockThreads (geometry p) 0) .block marked).trace[0]?).map (fun a => a.epoch.block) = some 1",
        })
        witnesses += """example : (warpThreads (geometry p) 0 15).contains 1023 = true := by decide
example : (blockThreads (geometry p) 0).contains 1024 = false := by decide
example : PartialWrites 64 ⟨.shared,0,0,2⟩ := by decide
example : (resume (blockThreads (geometry p) 0) .block start).pc 1023 = 1 := by decide
example : (resume (blockThreads (geometry p) 0) .block start).pc 1024 = 0 := by decide
example : ((resume (blockThreads (geometry p) 0) .block start).epochs 1023).block = 1 := by decide
example : ((resume (blockThreads (geometry p) 0) .block start).epochs 1024).block = 0 := by decide
example : (resume (blockThreads (geometry p) 0) .block marked).trace.length = 1 := by decide
example : ((resume (blockThreads (geometry p) 0) .block marked).trace[0]?).map (fun a => a.epoch.block) = some 0 := by decide
"""
    (project / "Witnesses.lean").write_text(base + witnesses)
    execute("positive-cast-and-preservation-witnesses", ["lake", "env", "lean", "Witnesses.lean"])
    for name, claim in claims.items():
        (project / (name + ".lean")).write_text(base + f"example : {claim} := by decide\n")
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    source_files = {p.relative_to(project).as_posix(): sha(p) for p in sorted(project.rglob("*"))
                    if p.is_file() and ".lake" not in p.parts and "__pycache__" not in p.parts}
    (out / "source-manifest.json").write_text(json.dumps(source_files, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in source_files:
            archive.add(project / name, arcname=name, recursive=False)
    shutil.copyfile(Path(__file__), out / "checker.py")
    shutil.copyfile(HERE / "check_program.py", out / "component_checker.py")
    report = {
        "schema": 1, "status": ("native-inout-first-block-checked" if block_stage else
                                 "native-inout-first-wave-checked" if wave_stage else "native-inout-scalar-prefix-checked"),
        "stage": args.stage, "local_lean_modules": len(own),
        "axiom_audits": audits, "false_claims_rejected": sum(not c["expected_accepted"] for c in checks),
        "checks": checks, "fresh_standalone_build": True, "frozen_python_reader_replayed": True,
        "source_archive_sha256": sha(out / "source.tar.gz"), "source_kernel_sha256": sha(CASE / "kernel.hip"),
        "scalar_prefix_execution_proved": True, "scalar_prefix_actual_trace_classification_proved": True,
        "scalar_prefix_race_freedom_proved": True, "scalar_prefix_instruction_count": 210,
        "scalar_prefix_access_count_per_lane": 64, "scalar_prefix_end_pc": 23,
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "canonical_source_equivalence_proved": False,
        "gpu_trials": 0, "model_calls": 0, "original_paper_fully_reproduced": False,
        "scope": "All rows1..255, valid lanes, arbitrary Ops/input/outside; actual seeded initialization and both rounds through first shuffle, all 16 rounded residual and unrounded shared stores, input preservation, source-order local square sum, actual-prefix trace classification/race freedom. Logical32 collectives, both barriers, normalized outputs, halt, scheduler/grid, canonical-real and IEEE equivalence remain open.",
    }
    if wave_stage:
        report.update({
            "first_native_wave_execution_proved": True, "first_native_wave_actual_trace_classification_proved": True,
            "first_native_wave_race_freedom_proved": True, "first_native_wave_end_pc": 35,
            "first_native_wave_physical_lanes": 64, "first_native_wave_logical_partition_width": 32,
            "first_native_wave_logical_partitions": 2, "first_native_wave_xor_stages": 5,
            "first_native_wave_partial_stores": 2,
            "scope": "All rows1..255, native waves0..15, arbitrary Ops/input/outside: actual seeded inout initialization and sequential lane folds, both 8-value rounds, five snapshot logical32 XOR/add stages inside physical64, separate lane0 results for both groups, two distinct partial stores, all lanes at first block barrier PC35, retained rounded residual/unrounded shared values and owned input cells, actual-wave classification/race freedom without RF assumptions. Composition across waves, barrier resume, second reduction, normalized outputs, halt/grid, canonical-real/IEEE equivalence and original-paper results remain open.",
        })
    if block_stage:
        report.update({
            "first_native_block_execution_prefix_proved": True,
            "first_native_block_actual_trace_classification_proved": True,
            "first_native_block_race_freedom_proved": True,
            "first_native_block_barrier_resume_proved": True,
            "first_native_block_participants": 1024, "first_native_block_physical_waves": 16,
            "first_native_block_partial_stores": 32, "first_native_block_residual_values": 16384,
            "first_native_block_unrounded_values": 16384,
            "first_native_block_pre_barrier_pc": 35, "first_native_block_resumed_pc": 36,
            "first_native_block_resumed_epoch": 1,
            "scope": "All rows1..255, valid blocks, arbitrary Ops/input/outside: actual seeded inout initialization, the block scheduler's sequential 16-wave fold, both 8-value rounds per lane, five logical32 snapshot XOR stages per wave, all32 partials, every rounded residual and separate unrounded shared value across all16384 columns, owned input preservation and readonly weights, all1024 participants converged at PC35, then actual runBlock barrier resume to PC36/epoch1 with memory and historical trace epochs unchanged. Actual-prefix classification/RF derived. Second reduction, normalization, second barrier, halt/grid, canonical-real/IEEE equivalence and original-paper results remain open.",
        })
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest = {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "local_lean_modules", "false_claims_rejected", "source_certificates")}), flush=True)


if __name__ == "__main__":
    main()
