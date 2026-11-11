"""Rebuild a native attention execution prefix outside Git, without model/GPU calls.

The stages check lane initialization, native first-block scheduling, and the
first query's scores, exponential denominator and output update. These are
execution prefixes, not whole-launch or source-reference certificates.
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
           "weights": "Lark.NativeAttentionWeights", "output": "Lark.NativeAttentionFirstOutput"}
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
    output_stage = args.stage == "output"
    weights_stage = args.stage in ("weights", "output")
    block_stage = args.stage != "lane"
    target = TARGETS[args.stage]
    names = OUTPUT_AUDITS if output_stage else WEIGHT_AUDITS if weights_stage else BLOCK_AUDITS if block_stage else LANE_AUDITS
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
    scope = ("native first block phase and resume, then a per-lane continuation from PC 21 through 119060 instructions "
             "to PC 83: first query row scores, weights, denominator, all weighted-V products and 256 output stores"
             if output_stage else
             "native first block phase and resume, then a per-lane continuation from PC 21 through 58891 instructions "
             "to PC 56: first query row scores, maximum, exponential weights and denominator" if weights_stage else
             "actual first runBlock phase, including 32 native lanes, block convergence and resume to PC 21"
             if block_stage else "actual runLane from PC 0 through 5405 instructions to first block barrier PC 20")
    remaining = ("Private-state stores, later query/key tiles, whole-launch execution and dense-reference equality remain unproved."
                 if output_stage else
                 "Output updates, later query/key tiles, whole-launch execution and dense-reference equality remain unproved."
                 if weights_stage else "It does not execute attention computation or later block phases, compose "
                 "the whole launch, or prove dense-reference equality.")
    (standalone / "README.md").write_text(
        f"# Native attention {args.stage} prefix proof\n\n"
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
        "schema": 1, "status": "native-output-prefix-checked" if output_stage else "native-weights-prefix-checked" if weights_stage else
                               "native-block-prefix-checked" if block_stage else "native-lane-prefix-checked",
        "stage": args.stage,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": scope,
        "groups": {"min": 1, "max": 65535}, "block": 32, "warp": 64,
        "prefix_instructions_per_lane": 119060 if output_stage else 58891 if weights_stage else 5405, "barrier_pc": 20,
        "initialization_instructions_per_lane": 5405,
        "instruction_count_start_pc": 21 if weights_stage else 0,
        "input_preservation_proved": True, "output_initialization_proved": True,
        "first_kv_row_copy_proved": True, "prefix_actual_trace_race_freedom_proved": True,
        "first_block_phase_and_resume_proved": block_stage,
        "all_block_outputs_initialized_proved": block_stage,
        "first_kv_tile_loaded_proved": block_stage,
        "barrier_resumption_proved": block_stage,
        "resumed_pc": 21 if block_stage else None,
        "block_epoch_increment": 1 if block_stage else 0,
        "first_query_scores_and_exponential_weights_proved": weights_stage,
        "first_query_denominator_proved": weights_stage,
        "query_preparation_instructions": 1030 if weights_stage else 0,
        "score_loop_instructions": 57666 if weights_stage else 0,
        "exponential_loop_instructions": 195 if weights_stage else 0,
        "compute_end_pc": 83 if output_stage else 56 if weights_stage else None,
        "later_query_tiles_proved": False, "later_key_tiles_proved": False,
        "weighted_value_product_proved": output_stage, "output_updates_proved": output_stage,
        "output_columns_proved": 256 if output_stage else 0,
        "weighted_value_terms_per_column": 32 if output_stage else 0,
        "output_loop_instructions": 60161 if output_stage else 0,
        "first_old_state_and_rescale_instructions": 8 if output_stage else 0,
        "half_conversion_sites_preserved": output_stage,
        "private_state_stores_proved": False,
        "arbitrary_scalar_operations": True, "axioms": audits,
        "fresh_standalone_build": True, "local_lean_modules": len(modules),
        "source_sha256": sha(CASE / "kernel.hip"),
        "source_archive_sha256": sha(out / "source.tar.gz"), "checks": records,
        "false_prefix_claims_rejected": len(controls),
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "whole_kernel_race_freedom_proved": False, "source_reference_equality_proved": False,
        "ieee_equivalence_proved": False, "original_paper_fully_reproduced": False,
        "gpu_trials": 0, "model_calls": 0,
    }
    write(out / "results.json", report)
    members = [p for p in sorted(out.iterdir()) if p.is_file()]
    write(out / "manifest.json", {p.name: sha(p) for p in members})
    print(json.dumps({k: report[k] for k in ("status", "prefix_instructions_per_lane", "local_lean_modules",
                                            "false_prefix_claims_rejected", "source_certificates")}))


if __name__ == "__main__":
    main()
