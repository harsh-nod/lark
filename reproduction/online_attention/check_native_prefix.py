"""Rebuild native attention execution proofs outside Git, without model/GPU calls.

The stages check lane initialization, native first-block scheduling, and the
first query's outputs, and a full first-key block computation and resume. These
are execution prefixes. The whole-launch stage checks actual execution and the
source-ordered online recurrence; the canonical real proof is checked separately.
"""

import argparse
from datetime import datetime, timezone
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
from lark_kernels import native_attention as native  # noqa: E402
from lark_kernels.ir import lean_node  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_fp16"
TARGETS = {"lane": "Lark.NativeAttentionFirstLane", "first-block": "Lark.NativeAttentionFirstResume",
           "weights": "Lark.NativeAttentionWeights", "output": "Lark.NativeAttentionFirstOutput",
           "first-key-block": "Lark.NativeAttentionFirstKeyBlock", "whole-launch": "Lark.NativeAttentionCorrect"}
LANE_AUDITS = ("first_lane_eq", "first_lane_run", "first_lane_output", "first_lane_tile", "first_lane_reads",
               "first_lane_good", "first_lane_race_free")
BLOCK_AUDITS = LANE_AUDITS + (
    "first_block_from_initial", "first_block_step", "first_resumed_pc", "first_resumed_epoch",
    "first_resumed_native", "first_resumed_reads", "first_resumed_output", "first_resumed_tile", "first_resumed_good",
)
WEIGHT_AUDITS = BLOCK_AUDITS + (
    "first_query_from_resumed", "dot_columns_eq", "dot_columns_value", "score_dot_eq", "score_rows_eq",
    "score_rows_maximum", "score_rows_value", "score_rows_good", "score_computation_eq", "first_scores_from_resumed",
    "exp_columns_eq", "exp_columns_sum", "exp_columns_value", "exp_columns_good", "exp_computation_eq",
    "first_weights_from_resumed", "first_weights_fields", "first_weights_values", "first_weights_reads", "first_weights_good",
    "first_weights_initial_prefix",
)
OUTPUT_AUDITS = WEIGHT_AUDITS + (
    "first_resumed_key", "old_selected_eq", "rescale_eq", "output_prepare_eq", "output_prepared_ready",
    "pv_cycle_eq", "pv_rows_eq", "pv_rows_value", "pv_computation_eq", "pv_computed_fields",
    "output_finish_eq", "output_column_eq", "output_columns_eq", "output_columns_value", "output_columns_good",
    "output_update_eq", "output_updated_value", "first_output_eq", "first_output_fields", "first_output_value",
    "first_output_reads", "first_output_good", "first_output_from_resumed", "first_output_initial_prefix",
)
KEY_AUDITS = OUTPUT_AUDITS + (
    "query_tail_eq", "query_tail_values", "query_tail_global", "query_tail_good",
    "first_query_complete_eq", "first_query_complete_private", "first_query_complete_output",
    "row_scores_eq", "row_scores_fields", "row_scores_values", "row_scores_good",
    "row_weights_eq", "row_weights_fields", "row_weights_values", "row_weights_good",
    "row_output_eq", "row_output_value", "row_output_good",
    "query_row_eq", "query_row_value", "query_row_private", "query_row_native", "query_row_reads", "query_row_tiles", "query_row_good",
    "query_rows_eq", "query_rows_value", "query_rows_private", "query_rows_reads", "query_rows_good",
    "query_tile_fuel", "query_tile_run", "query_tile_eq", "query_tile_value", "query_tile_private", "query_tile_good",
    "eval_expr_frame", "execute_lane_other", "run_lane_other", "query_tile_ready_other",
    "query_fold_run", "query_fold_member", "query_fold_value", "query_fold_private", "query_fold_good",
    "query_block_warp", "query_block_step", "query_resumed_pc", "query_resumed_epoch", "query_resumed_value",
    "query_resumed_private", "query_resumed_reads", "query_resumed_good",
    "first_key_block_reduction", "first_key_resumed_epoch", "first_key_resumed_member", "first_key_resumed_value",
    "first_key_resumed_private", "first_key_resumed_good", "first_key_block_initial",
)
LAUNCH_AUDITS = KEY_AUDITS + (
    "next_entry_eq", "next_load_eq", "next_load_run", "next_load_value", "next_load_good", "next_load_memory_other",
    "next_fold_run", "next_fold_member", "next_fold_tile", "next_fold_memory_other", "next_fold_good",
    "next_block_warp", "next_block_step", "next_resumed_pc", "next_resumed_epoch", "next_resumed_queries", "next_resumed_tiles", "next_resumed_good",
    "halt_lane_eq", "halt_lane_run", "halt_fold_frames", "halt_fold_member", "halt_block_run",
    "query_phase_done", "copy_phase_start", "initial_query_start", "keys_completed_spec", "keys_completed_reduction",
    "final_block_run", "final_block_member", "final_block_values", "final_block_private", "final_block_reads", "final_block_good", "final_block_initial",
    "first_resumed_foreign", "query_resumed_foreign", "keys_completed_foreign", "final_block_foreign",
    "keys_completed_output_foreign", "final_block_output_foreign", "full_blocks_run", "full_blocks_reads_good", "full_blocks_pc", "full_blocks_value",
    "grid_run", "grid_pc", "grid_value", "grid_reads_good", "grid_race_free", "source_extract_of_values", "grid_extract", "source_order_correct",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def closure(module, found=None):
    found = set() if found is None else found
    if module in found:
        return found
    require(re.fullmatch(r"Lark\.[A-Za-z0-9_]+", module), "Unexpected module: " + module)
    found.add(module)
    source = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    for line in source.read_text().splitlines():
        if line.startswith("import "):
            for dependency in line.split()[1:]:
                if dependency.startswith("Lark."):
                    closure(dependency, found)
                else:
                    require(dependency == "Std", "Unexpected external import: " + dependency)
    return found


def check(cwd, command, dest, expected=True, timeout=300):
    before = time.monotonic()
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    log = result.stdout + result.stderr
    dest.write_text(log)
    if expected:
        require(result.returncode == 0 and "error:" not in log and "sorryAx" not in log,
                "Positive Lean check failed: " + str(dest))
    else:
        require(result.returncode != 0 and "error:" in log and "is false" in log,
                "Control did not reach its false assertion: " + str(dest))
    return {"name": dest.stem, "accepted": result.returncode == 0,
            "expected_accepted": expected, "exit_code": result.returncode,
            "timed_out": False, "seconds": time.monotonic() - before}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stage", choices=tuple(TARGETS), default="lane")
    args = parser.parse_args()
    launch_stage = args.stage == "whole-launch"
    key_stage = args.stage in ("first-key-block", "whole-launch")
    output_stage = args.stage in ("output", "first-key-block", "whole-launch")
    weights_stage = args.stage in ("weights", "output", "first-key-block", "whole-launch")
    block_stage = args.stage != "lane"
    target = TARGETS[args.stage]
    names = LAUNCH_AUDITS if launch_stage else KEY_AUDITS if key_stage else OUTPUT_AUDITS if output_stage else WEIGHT_AUDITS if weights_stage else BLOCK_AUDITS if block_stage else LANE_AUDITS
    out = args.output.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)),
            "Choose --output outside a Git checkout for the standalone check")
    out.mkdir(parents=True, exist_ok=False)
    standalone = out / "source"
    standalone.mkdir()
    task = native.parse_task((CASE / "task.json").read_text())
    source = (CASE / "kernel.hip").read_bytes().decode()
    native.check_reference((CASE / "reference.py").read_text(), task)
    provenance = json.loads((HERE / "native-provenance.json").read_text())
    require(sha(CASE / "kernel.hip") == provenance["native_source_sha256"], "Native source changed")
    translated = native.translate(source, task)
    modules = sorted(closure(target))
    for module in modules:
        name = module.replace(".", "/") + ".lean"
        dest = standalone / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean" / name, dest)
    shutil.copyfile(ROOT / "lean/lean-toolchain", standalone / "lean-toolchain")
    (standalone / "lakefile.toml").write_text(
        'name = "native_attention_prefix"\nversion = "0.1.0"\n'
        f'defaultTargets = ["{target}"]\n\n[[lean_lib]]\nname = "Lark"\n')
    header = f"import {target}\nopen LarkNonlinear LarkNativeAttention\n"
    binding = header + """set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
def sourceProgram : List Instr := [
""" + ",\n".join(lean_node(i) for i in translated.program) + f"""
]
def sourceShared : List Nat := {[size for _, size in translated.shared]}
def sourceLocals : List Nat := {[size for _, size in translated.locals]}
theorem source_binding (p : Shape) : sourceProgram = program ∧
    sourceShared = (layout p).shared ∧ sourceLocals = (layout p).locals :=
  ⟨by decide, rfl, rfl⟩
theorem source_geometry (p : Shape) : geometry p = ⟨p.groups, {task.block}, {task.warp}⟩ := rfl
theorem source_fuel : fuel = ⟨{', '.join(str(x) for x in native.FUEL)}⟩ := by decide
#print axioms source_binding
""" + "\n".join("#print axioms " + n for n in names) + "\n"
    (standalone / "Main.lean").write_text(binding)
    controls = {
        "wrong-barrier-pc": """
example (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstLane ops input t s).pc t = 21 := by
  rw [(first_lane_fields ops input t s).1]
  decide
""",
        "nonzero-initialized-output": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t : Nat) (s : State Nat)
    (hz : zeroValue ops = 0) :
    (firstLane ops input t s).memory (globalCell 0 (globalAddress t 0 0)) = some 1 := by
  rw [first_lane_output ops input t 0 0 s (by decide) (by decide), hz]
  decide
""",
        "wrong-copied-key-value": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t : Nat) (s : State Nat)
    (hv : ops.fromHalf (input 2 (globalAddress t 0 0)) = 0) :
    (firstLane ops input t s).memory (sharedCell t 1 (sharedAddress t 0)) = some 1 := by
  rw [first_lane_tile ops input t 1 0 s (Or.inl rfl) (by decide), hv]
  decide
""",
    }
    if block_stage:
        controls.update({
            "wrong-resumed-pc": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) : (firstResumed p ops input b s).pc t = 20 := by
  rw [first_resumed_pc p ops input b t s ht]
  decide
""",
            "missing-block-epoch-bump": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (b t : Nat) (ht : t ∈ blockThreads (geometry p) b) :
    ((firstResumed p ops input b (initial (layout p) input outside)).epochs t).block = 0 := by
  rw [first_resumed_epoch p ops input b t (initial (layout p) input outside) ht]
  change 1 = 0
  decide
""",
            "wrong-block-key-value": """
example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat) (b t : Nat) (s : State Nat)
    (ht : t ∈ blockThreads (geometry p) b) (hv : ops.fromHalf (input 2 (globalAddress t 0 0)) = 0) :
    (firstResumed p ops input b s).memory (sharedCell t 1 (sharedAddress t 0)) = some 1 := by
  rw [first_resumed_tile p ops input b t 1 0 s ht (Or.inl rfl) (by decide), hv]
  decide
""",
        })
    if weights_stage:
        controls.update({
            "wrong-weight-prefix-pc": """
example (ops : Ops α) (input : Nat → Nat → α) (t keyTile : Nat) (s : State α) :
    (firstWeights ops input t keyTile s).pc t = 55 := by
  rw [(first_weights_fields ops input t keyTile s).1]
  decide
""",
            "wrong-exponential-weight": """
example (ops : Ops Nat) (t : Nat) (values : Nat → Nat) (maximum : Nat) (s : State Nat)
    (hw : normalizedWeight ops (values 0) maximum = 0) :
    (weightsComputed ops t values maximum s).memory (sharedCell t 3 (scoreAddress t 0)) = some 1 := by
  rw [weights_computed_value ops t values 0 maximum s (by decide), hw]
  decide
""",
            "wrong-denominator-value": """
example (ops : Ops Nat) (t : Nat) (values : Nat → Nat) (maximum : Nat) (s : State Nat)
    (hd : expFold ops values maximum 0 32 (ops.literal 0 1) = 0) :
    (weightsComputed ops t values maximum s).regs t 5 = some 1 := by
  rw [(weights_computed_fields ops t values maximum s).2.2.1, hd]
  decide
""",
        })
    if output_stage:
        controls.update({
            "wrong-output-prefix-pc": """
example (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstOutput ops input t s).pc t = 82 := by
  rw [(first_output_fields ops input t s).1]
  decide
""",
            "wrong-weighted-value-accumulator": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t key col : Nat) (weights : Nat → Nat) (s : State Nat)
    (hv : pvValue ops input t key col weights = 0) :
    (pvComputed ops input t key col weights s).regs t 13 = some 1 := by
  rw [(pv_computed_fields ops input t key col weights s).2.1, hv]
  decide
""",
            "wrong-half-output-store": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t qi key col : Nat) (weights : Nat → Nat)
    (scales : ScaleValues Nat) (oldMass oldStored : Nat) (s : State Nat)
    (hv : storedOutput ops scales oldMass oldStored (pvValue ops input t key col weights) = 0) :
    (outputColumn ops input t qi key col weights scales oldMass oldStored s).memory
      (globalCell 0 (globalAddress t qi col)) = some 1 := by
  rw [output_column_memory, if_pos rfl, hv]
  decide
""",
            "wrong-first-output-value": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t : Nat) (s : State Nat)
    (hv : firstOutputValues ops input t 0 = 0) :
    (firstOutput ops input t s).memory (globalCell 0 (globalAddress t 0 0)) = some 1 := by
  rw [first_output_value ops input t 0 s (by decide), hv]
  decide
""",
            "wrong-initial-key-counter": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).indices t 5 = some 1 := by
  rw [first_resumed_key p ops input b t s ht]
  decide
""",
        })
    if key_stage:
        controls.update({
            "wrong-full-query-lane-pc": """
example (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstKeyLane ops input t s).pc t = 83 := by
  rw [(first_key_lane_fields ops input t s).1]
  decide
""",
            "wrong-subsequent-key-fuel": """
example : queryTileFuel 1 = 476254 := by
  rw [query_tile_fuel]
  decide
""",
            "missing-private-mass-store": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t key : Nat) (old : Nat → QueryValue Nat) (s : State Nat)
    (hv : (nextQueryValue ops input t 3 key (old 3)).mass = 0) :
    (queryTile ops input t key old s).memory (privateCell t 1 3) = some 1 := by
  rw [(query_tile_private ops input t key 3 old s (by decide)).2, hv]
  decide
""",
            "wrong-last-query-block-output": """
example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat) (b t : Nat) (s : State Nat)
    (ht : t ∈ blockThreads (geometry p) b) (hv : (firstKeyValues ops input t 3).stored 255 = 0) :
    (firstKeyResumed p ops input b s).memory (globalCell 0 (globalAddress t 3 255)) = some 1 := by
  rw [first_key_resumed_value p ops input b t 3 255 s ht (by decide) (by decide), hv]
  decide
""",
            "wrong-second-resume-pc": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (b t : Nat) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b) :
    (firstKeyResumed p ops input b (initial (layout p) input outside)).pc t = 87 := by
  rw [(first_key_resumed_member p ops input outside b t hb ht).1]
  decide
""",
            "missing-second-epoch-bump": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (b t : Nat) (hb : b < p.groups) (ht : t ∈ blockThreads (geometry p) b) :
    ((firstKeyResumed p ops input b (initial (layout p) input outside)).epochs t).block = 1 := by
  rw [(first_key_resumed_member p ops input outside b t hb ht).2.2.2]
  decide
""",
            "wrong-block-private-maximum": """
example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat) (b t : Nat) (s : State Nat)
    (ht : t ∈ blockThreads (geometry p) b) (hv : (firstKeyValues ops input t 3).maximum = 0) :
    (firstKeyResumed p ops input b s).memory (privateCell t 0 3) = some 1 := by
  rw [(first_key_resumed_private p ops input b t 3 s ht (by decide)).1, hv]
  decide
""",
        })
    if launch_stage:
        controls.update({
            "wrong-next-load-pc": """
example (ops : Ops α) (input : Nat → Nat → α) (t key : Nat) (s : State α) :
    (nextLoad ops input t key s).pc t = 21 := by
  rw [(next_load_fields ops input t key s).1]
  decide
""",
            "wrong-final-key-counter": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) : (finalBlock p ops input b s).indices t 5 = some 3 := by
  rw [(final_block_member p ops input b t s ht).2]
  decide
""",
            "wrong-block-halt-pc": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b t : Nat) (s : State α)
    (ht : t ∈ blockThreads (geometry p) b) : (finalBlock p ops input b s).pc t = 88 := by
  rw [(final_block_member p ops input b t s ht).1]
  decide
""",
            "wrong-grid-halt-pc": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t : Nat) (ht : t < p.groups * 32) : (gridState p ops input (initial (layout p) input outside)).pc t = 88 := by
  rw [grid_pc p ops input outside t ht]
  decide
""",
            "wrong-final-grid-output": """
example (p : Shape) (ops : Ops Nat) (input : Nat → Nat → Nat) (outside : Location → Option Nat)
    (offset : Nat) (hi : offset < p.groups * 32768) (hv : outputValue ops input offset = 0) :
    (gridState p ops input (initial (layout p) input outside)).memory (globalCell 0 offset) = some 1 := by
  rw [grid_value p ops input outside offset hi, hv]
  decide
""",
            "wrong-extracted-output-length": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) :
    (sourceSpec ⟨1, by decide, by decide⟩ ops input).length = 32767 := by
  simp only [sourceSpec, List.length_map, List.length_range]
  decide
""",
            "wrong-grid-race-result": """
example (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (geometry p) (gridState p ops input (initial (layout p) input outside)).trace = false := by
  rw [grid_race_free p ops input outside]
  decide
""",
            "wrong-next-key-copy-value": """
example (ops : Ops Nat) (input : Nat → Nat → Nat) (t key : Nat) (s : State Nat)
    (hv : ops.fromHalf (input 2 (globalAddress t (key + 1) 255)) = 0) :
    (nextLoad ops input t key s).memory (sharedCell t 1 (sharedAddress t 255)) = some 1 := by
  rw [next_load_value ops input t key 1 255 s (Or.inl rfl) (by decide), hv]
  decide
""",
        })
    for name, content in controls.items():
        (standalone / (name + ".lean")).write_text(header + content)
    frozen = standalone / "native-source"
    frozen.mkdir()
    for path in sorted(CASE.iterdir()):
        if path.is_file():
            shutil.copyfile(path, frozen / path.name)
    shutil.copyfile(HERE / "native-provenance.json", frozen / "native-provenance.json")
    shutil.copyfile(HERE / "upstream/LICENSE", frozen / "UPSTREAM-LICENSE")
    shutil.copyfile(ROOT / "LICENSE", standalone / "LICENSE")
    shutil.copyfile(Path(__file__), out / "checker.py")
    scope = ("actual full native runLaunch for every allowed group count: all four keys, nine block phases, full grid halt, "
             "all outputs extracted against the source-ordered online recurrence, input preservation and actual trace race freedom"
             if launch_stage else
             "actual first two native runBlock phases and barrier resumes to PC 88: all 32 lanes and all four query rows "
             "for key tile zero, including all output/private state stores, input preservation and prefix trace race freedom"
             if key_stage else
             "native first block phase and resume, then a per-lane continuation from PC 21 through 119060 instructions "
             "to PC 83: first query row scores, weights, denominator, all weighted-V products and 256 output stores"
             if output_stage else
             "native first block phase and resume, then a per-lane continuation from PC 21 through 58891 instructions "
             "to PC 56: first query row scores, maximum, exponential weights and denominator" if weights_stage else
             "actual first runBlock phase, including 32 native lanes, block convergence and resume to PC 21"
             if block_stage else "actual runLane from PC 0 through 5405 instructions to first block barrier PC 20")
    remaining = ("Canonical dense-real equality is checked separately with Mathlib. No IEEE equivalence or error bound, NVIDIA execution or original-paper completion is claimed."
                 if launch_stage else
                 "The three later key tiles, their copy/barrier phases, whole-launch execution and dense-reference equality remain unproved."
                 if key_stage else
                 "Private-state stores, later query/key tiles, whole-launch execution and dense-reference equality remain unproved."
                 if output_stage else
                 "Output updates, later query/key tiles, whole-launch execution and dense-reference equality remain unproved."
                 if weights_stage else "It does not execute attention computation or later block phases, compose "
                 "the whole launch, or prove dense-reference equality.")
    (standalone / "README.md").write_text(
        f"# Native attention {args.stage} {'proof' if launch_stage else 'prefix proof'}\n\n"
        "Run `lake build`, then `lake env lean Main.lean` with Lean 4.19.0.\n"
        f"The {len(controls)} other top-level Lean files intentionally fail at false postconditions.\n"
        f"Scope: {scope}.\n"
        + remaining + "\n")
    source_paths = sorted(p for p in standalone.rglob("*") if p.is_file())
    write(out / "source-manifest.json", {str(p.relative_to(standalone)): sha(p) for p in source_paths})
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for path in source_paths:
            info = archive.gettarinfo(str(path), arcname=str(path.relative_to(standalone)))
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ""
            with path.open("rb") as stream:
                archive.addfile(info, stream)
    records = [check(standalone, ["lake", "build"], out / "build.log")]
    records.append(check(standalone, ["lake", "env", "lean", "Main.lean"], out / "main.log"))
    for name in controls:
        records.append(check(standalone, ["lake", "env", "lean", name + ".lean"], out / (name + ".log"), False))
    log = (out / "main.log").read_text()
    audits = {}
    for name in names:
        entries = re.findall(r"^'LarkNativeAttention\." + name +
                             r"' depends on axioms: \[([^]]*)\]$", log, re.M)
        require(len(entries) == 1, "Missing or ambiguous axiom audit: " + name)
        axioms = entries[0].split(", ") if entries[0] else []
        require(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
        audits[name] = axioms
    report = {
        "schema": 1, "status": "native-whole-launch-checked" if launch_stage else "native-first-key-block-prefix-checked" if key_stage else
                               "native-output-prefix-checked" if output_stage else "native-weights-prefix-checked" if weights_stage else
                               "native-block-prefix-checked" if block_stage else "native-lane-prefix-checked",
        "stage": args.stage,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": scope,
        "groups": {"min": 1, "max": 65535}, "block": 32, "warp": 64,
        "prefix_instructions_per_lane": 1914303 if launch_stage else 476254 if key_stage else 119060 if output_stage else 58891 if weights_stage else 5405, "barrier_pc": 20,
        "initialization_instructions_per_lane": 5405,
        "instruction_count_start_pc": 0 if launch_stage else 21 if weights_stage else 0,
        "input_preservation_proved": True, "output_initialization_proved": True,
        "first_kv_row_copy_proved": True, "prefix_actual_trace_race_freedom_proved": True,
        "first_block_phase_and_resume_proved": block_stage,
        "all_block_outputs_initialized_proved": block_stage,
        "first_kv_tile_loaded_proved": block_stage,
        "barrier_resumption_proved": block_stage,
        "resumed_pc": None if launch_stage else 88 if key_stage else 21 if block_stage else None,
        "block_epoch_increment": 8 if launch_stage else 2 if key_stage else 1 if block_stage else 0,
        "first_query_scores_and_exponential_weights_proved": weights_stage,
        "first_query_denominator_proved": weights_stage,
        "query_preparation_instructions": 16468 if launch_stage else 4117 if key_stage else 1030 if weights_stage else 0,
        "score_loop_instructions": 922656 if launch_stage else 230664 if key_stage else 57666 if weights_stage else 0,
        "exponential_loop_instructions": 3120 if launch_stage else 780 if key_stage else 195 if weights_stage else 0,
        "compute_end_pc": 90 if launch_stage else 87 if key_stage else 83 if output_stage else 56 if weights_stage else None,
        "later_query_tiles_proved": launch_stage, "later_key_tiles_proved": launch_stage,
        "weighted_value_product_proved": output_stage, "output_updates_proved": output_stage,
        "output_columns_proved": 4096 if launch_stage else 1024 if key_stage else 256 if output_stage else 0,
        "weighted_value_terms_per_column": 32 if output_stage else 0,
        "output_loop_instructions": 962576 if launch_stage else 240644 if key_stage else 60161 if output_stage else 0,
        "first_old_state_and_rescale_instructions": 152 if launch_stage else 32 if key_stage else 8 if output_stage else 0,
        "half_conversion_sites_preserved": output_stage,
        "private_state_stores_proved": key_stage,
        "all_query_rows_for_first_key_tile_proved": key_stage,
        "first_key_compute_phase_and_resume_proved": key_stage,
        "completed_block_phases": 9 if launch_stage else 2 if key_stage else 1 if block_stage else 0,
        "first_key_output_stores_per_block": 32768 if key_stage else 0,
        "lane_fuel": 1000000, "lane_fuel_changed": False,
        "private_state_and_query_tail_instructions": 64 if launch_stage else 16 if key_stage else 0,
        "query_exit_guard_instructions": 4 if launch_stage else 1 if key_stage else 0,
        "later_kv_copy_instructions": 3855 if launch_stage else 0,
        "final_halt_instructions": 3 if launch_stage else 0,
        "whole_grid_halt_proved": launch_stage,
        "all_outputs_extracted_proved": launch_stage,
        "source_ordered_recurrence_equality_proved": launch_stage,
        "subsequent_key_lane_instruction_count": 476262 if key_stage else None,
        "arbitrary_scalar_operations": True, "axioms": audits,
        "fresh_standalone_build": True, "local_lean_modules": len(modules),
        "source_sha256": sha(CASE / "kernel.hip"),
        "source_archive_sha256": sha(out / "source.tar.gz"), "checks": records,
        "false_prefix_claims_rejected": len(controls),
        "source_certificates": 0, "whole_kernel_execution_proved": launch_stage,
        "whole_kernel_race_freedom_proved": launch_stage, "source_reference_equality_proved": False,
        "canonical_dense_reference_equality_proved": False,
        "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
        "gpu_trials": 0, "model_calls": 0,
    }
    if launch_stage:
        parts = ("initialization_instructions_per_lane", "query_preparation_instructions", "score_loop_instructions",
                 "exponential_loop_instructions", "first_old_state_and_rescale_instructions", "output_loop_instructions",
                 "private_state_and_query_tail_instructions", "query_exit_guard_instructions", "later_kv_copy_instructions", "final_halt_instructions")
        require(sum(report[k] for k in parts) == report["prefix_instructions_per_lane"], "Inconsistent whole-launch source instruction accounting")
    write(out / "results.json", report)
    members = [p for p in sorted(out.iterdir()) if p.is_file()]
    write(out / "manifest.json", {p.name: sha(p) for p in members})
    print(json.dumps({k: report[k] for k in ("status", "prefix_instructions_per_lane", "local_lean_modules",
                                            "false_prefix_claims_rejected", "source_certificates")}))


if __name__ == "__main__":
    main()
