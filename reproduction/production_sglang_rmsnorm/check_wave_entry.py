"""Fresh complete native wave preparation and first logical32 XOR snapshot.

This stage executes one snapshot; later reduction steps and all shared stores remain unproved.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time

import check_program as components

ROOT, HERE = components.ROOT, components.HERE
TARGET = "Lark.NativeSglangRmsNormWaveEntry"


def statement(source, task, repaired):
    header = components.statement(source, task, repaired).split("theorem source_output_coverage", 1)[0]
    header = header.replace(components.TARGET, TARGET)
    text = header + 'attribute [local irreducible] prefixFold prefixState\ntheorem source_carried_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)\n    (ht : t < sourceShape.rows * 1024) (hp : s.pc t = 0) (reads : Reads sourceShape input s) :\n    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t fuel.lane s =\n      some (prefixState ops input t s) := by\n  rw [source_binding.1]\n  exact carried_prefix_run sourceShape sourceRepaired ops input t s ht hp reads\ntheorem source_memory_frame (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :\n    ThreadFrame t s (prefixState ops input t s) := prefix_frame ops input t s\ntheorem source_fold_execution (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)\n    (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < sourceShape.rows * 1024)\n    (hp : ∀ t ∈ ts, s.pc t = 0) (reads : Reads sourceShape input s) :\n    ts.foldlM (fun s t => LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape)\n      sourceProgram t fuel.lane s) s = some (prefixFold ops input ts s) := by\n  rw [source_binding.1]\n  exact prefix_fold_run sourceShape sourceRepaired ops input ts s hn ht hp reads\ntheorem source_wave_entry_success (ops : Ops α) (input : Nat → Nat → α)\n    (row warp : Nat) (s : State α) (hr : row < sourceShape.rows) (hw : warp < 16)\n    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads sourceShape input s) :\n    ((warpThreads (geometry sourceShape) row warp).foldlM\n      (fun u t => LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t fuel.lane u) s).bind\n      (fun prepared => LarkPartitionCollective.runShuffle (geometry sourceShape) sourceProgram\n        (cohortThreads row warp 64) prepared) = some (firstSnapshot sourceShape ops input row warp s) := by\n  rw [source_binding.1]\n  exact wave_entry_success sourceShape sourceRepaired ops input row warp s hr hw hp reads\ntheorem source_native_warp_transition (ops : Ops α) (input : Nat → Nat → α)\n    (row warp : Nat) (s : State α) (hr : row < sourceShape.rows) (hw : warp < 16)\n    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads sourceShape input s) :\n    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram\n      (warpThreads (geometry sourceShape) row warp) fuel.warp s =\n    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram\n      (cohortThreads row warp 64) 7 (firstSnapshot sourceShape ops input row warp s) := by\n  rw [source_binding.1]\n  exact wave_first_snapshot_step sourceShape sourceRepaired ops input row warp 7 s hr hw hp reads\ntheorem source_snapshot_values (ops : Ops α) (input : Nat → Nat → α)\n    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads sourceShape input s) :\n    (firstSnapshot sourceShape ops input row warp s).pc (cohortBase row warp + lane) = 45 ∧\n    (firstSnapshot sourceShape ops input row warp s).regs (cohortBase row warp + lane) 0 =\n      some (threadSum ops input row (warp * 64 + lane)) ∧\n    (firstSnapshot sourceShape ops input row warp s).regs (cohortBase row warp + lane) 1 =\n      some (threadSum ops input row (warp * 64 + xorPeer32 lane 16)) :=\n  wave_snapshot_values sourceShape ops input row warp lane s hw hl reads\ntheorem source_cached_halves (ops : Ops α) (input : Nat → Nat → α)\n    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads sourceShape input s) :\n    let t := cohortBase row warp + lane\n    InputPrefix input row (warp * 64 + lane) 16 t (firstSnapshot sourceShape ops input row warp s) ∧\n    WeightPrefix input (warp * 64 + lane) 16 t (firstSnapshot sourceShape ops input row warp s) :=\n  wave_snapshot_caches sourceShape ops input row warp lane s hw hl reads\ntheorem source_readonly_globals (ops : Ops α) (input : Nat → Nat → α)\n    (row warp : Nat) (s : State α) (reads : Reads sourceShape input s) :\n    Reads sourceShape input (firstSnapshot sourceShape ops input row warp s) :=\n  wave_snapshot_reads sourceShape ops input row warp s reads\ntheorem source_snapshot_preserves (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :\n    (firstSnapshot sourceShape ops input row warp s).memory = (wavePrepared ops input row warp s).memory ∧\n    (firstSnapshot sourceShape ops input row warp s).indices = (wavePrepared ops input row warp s).indices ∧\n    (firstSnapshot sourceShape ops input row warp s).epochs = s.epochs ∧\n    (firstSnapshot sourceShape ops input row warp s).trace = (wavePrepared ops input row warp s).trace :=\n  wave_snapshot_preserves sourceShape ops input row warp s\ntheorem source_past_trace (ops : Ops α) (input : Nat → Nat → α)\n    (row warp : Nat) (s : State α) (reads : Reads sourceShape input s) :\n    ∃ events, (firstSnapshot sourceShape ops input row warp s).trace = events ++ s.trace ∧\n      events.length = 5120 ∧ (∀ a ∈ events, Good a) :=\n  wave_snapshot_trace_tail sourceShape ops input row warp s reads\ntheorem source_trace_length (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :\n    (firstSnapshot sourceShape ops input row warp s).trace.length = s.trace.length + 5120 :=\n  wave_snapshot_trace_length sourceShape ops input row warp s\ntheorem source_complete_partitions (row warp : Nat) (hw : warp < 16) :\n    LarkPartitionCollective.completePartitions (geometry sourceShape) (cohortThreads row warp 64) 32 = true :=\n  cohort_complete32 sourceShape row warp 64 hw (Or.inr rfl)\ntheorem source_initial_snapshot_race_free (ops : Ops α) (input : Nat → Nat → α)\n    (outside : Location → Option α) (row warp : Nat) :\n    raceFree (geometry sourceShape) (firstSnapshot sourceShape ops input row warp (initial sourceShape input outside)).trace = true :=\n  initial_wave_snapshot_race_free sourceShape ops input outside row warp\ntheorem source_peer_stays_partition (lane mask : Nat) (hl : lane < 64) (hm : mask < 32) :\n    xorPeer32 lane mask / 32 = lane / 32 := xor_peer_partition lane mask hl hm\ntheorem source_first_shuffle_site : sourceProgram[44]? = some (.shuffle .xor 1 0 (.const 16) 32) := by\n  rw [source_binding.1]\n  decide\n'
    names = ['source_binding', 'source_carried_lane', 'source_memory_frame', 'source_fold_execution', 'source_wave_entry_success', 'source_native_warp_transition', 'source_snapshot_values', 'source_cached_halves', 'source_readonly_globals', 'source_snapshot_preserves', 'source_past_trace', 'source_trace_length', 'source_complete_partitions', 'source_initial_snapshot_race_free', 'source_peer_stays_partition', 'source_first_shuffle_site']
    return text + "".join("#print axioms " + name + "\n" for name in names)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh standalone output outside repository required")
    out.mkdir(parents=True, exist_ok=False)
    lake = str(args.lean_bin.resolve() / "lake")
    if "Lean version 4.19.0" not in subprocess.check_output([lake, "--version"], text=True):
        raise ValueError("Pinned Lean/Lake4.19.0 required")
    own = {}
    components.modules(TARGET, own)
    if len(own) != 33 or sum(s.count("#print axioms ") for s in own.values()) != 260:
        raise ValueError("Unexpected scalar prefix closure")
    source = out / "source"
    files = ["lean/" + name.replace(".", "/") + ".lean" for name in own]
    files += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    files += [str(p.relative_to(ROOT)) for p in (ROOT / "lark_kernels").glob("*.py")]
    files += [str(p.relative_to(ROOT)) for p in HERE.glob("*.py")]
    files += [str(p.relative_to(ROOT)) for folder in ("cases", "upstream") for p in (HERE / folder).rglob("*") if p.is_file()]
    files += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for name in sorted(set(files)):
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, dest)
        hashes[name] = components.sha(dest)
    (out / "source-manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in hashes:
            archive.add(source / name, arcname=name, recursive=False)
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    checks, audits = [], {}

    def run(name, command, accepted=True, count=None):
        start = time.monotonic()
        result = subprocess.run(command, cwd=source / "lean", env=env, capture_output=True, text=True, timeout=600 if name == "fresh-build" else 180)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        if (result.returncode == 0) is not accepted:
            raise ValueError("Unexpected prefix proof result: " + name + ": " + log)
        if accepted:
            entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
            found = {k: [a.strip() for a in v.split(",") if a.strip()] for k, v in entries}
            if (len(entries) != len(found) or len(found) != count
                    or any(not set(v) <= {"propext", "Classical.choice", "Quot.sound"} for v in found.values())):
                raise ValueError("Prefix axiom closure differs: " + name)
            audits[name] = found
        elif "is false" not in log or re.search(r"maximum recursion|heartbeats|stack overflow|timed out|out of memory", log, re.I):
            raise ValueError("False prefix claim did not fail logically: " + name)
        checks.append({"name": name, "accepted": accepted, "exit_code": result.returncode, "seconds": time.monotonic() - start})

    run("fresh-build", [lake, "build", TARGET], count=260)
    for variant, repaired in (("native_original", False), ("native_fixed", True)):
        case = HERE / "cases" / variant
        text = (case / "kernel.hip").read_text()
        components.native.check_reference((case / "reference.py").read_text())
        for rows in (1, 3, 131072):
            data = json.loads((case / "task.json").read_text())
            data["launch"]["grid"] = rows
            data["buffers"][0]["shape"][0] = data["buffers"][1]["shape"][0] = rows
            task = components.native.parse_task(json.dumps(data))
            name = variant + "_rows_" + str(rows)
            (source / "lean" / (name + ".lean")).write_text(statement(text, task, repaired))
            run(name, [lake, "env", "lean", name + ".lean"], count=16)
    case = HERE / "cases/native_fixed"
    text = (case / "kernel.hip").read_text()
    task = components.native.parse_task((case / "task.json").read_text())
    changes = {
        "aliased-input-cache-slot": text.replace("input_values[input_slot] =", "input_values[0] =", 1),
        "wrong-input-cache-address": text.replace("input[input_address]", "input[input_column]", 1),
        "aliased-weight-cache-slot": text.replace("weight_values[weight_slot] =", "weight_values[0] =", 1),
        "wrong-weight-cache-address": text.replace("weight[weight_column]", "weight[weight_slot]", 1),
        "wrong-pair-grouping": text.replace("sum = sum + pair_square;", "sum = (sum + xx) + yy;", 1),
        "wrong-first-shuffle": text.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
    }
    controls = {name: statement(changed, task, True) for name, changed in changes.items() if changed != text}
    if len(controls) != 6:
        raise ValueError("Unchanged cache source control")
    header = f'''import {TARGET}
open LarkNonlinear LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold prefixState
def p : Shape := ⟨1,by decide,by decide⟩
def ops : Ops Nat := ⟨fun i _ => i.toNat,Nat.add,Nat.sub,Nat.mul,Nat.max,Nat.div,id,id,id,id,id⟩
def input (_ i : Nat) := i
def base := initial p input (fun _ => none)
def prior : State Nat := {{base with trace := [⟨999,globalCell 0 0,true,{{}}⟩]}}
'''
    controls["crossed-logical-partition"] = header + "example : xorPeer32 31 16 = 47 := by decide\n"
    controls["invented-full-reduction-pc"] = header + '''example : (firstSnapshot p ops input 0 0 base).pc 0 = 54 := by
  have h := wave_snapshot_values p ops input 0 0 0 base (by decide) (by decide) (initial_reads p input (fun _ => none))
  have hpc : (firstSnapshot p ops input 0 0 base).pc 0 = 45 := by
    simpa only [cohortBase,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using h.1
  rw [hpc]
  decide
'''
    controls["erased-prior-trace"] = header + '''example : (firstSnapshot p ops input 0 0 prior).trace.length = 5120 := by
  rw [wave_snapshot_trace_length]
  decide
'''
    controls["invented-block-barrier"] = header + '''example : ((firstSnapshot p ops input 0 0 base).epochs 0).block = 1 := by
  rw [(wave_snapshot_preserves p ops input 0 0 base).2.2.1]
  decide
'''
    controls["corrupted-other-thread-cache"] = header + '''example : (prefixState ops input 0 base).memory (privateCell 1 0 0) = some 0 := by
  rw [(prefix_frame ops input 0 base).memory _ (Or.inr (Or.inl (by decide)))]
  decide
'''
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {
        "schema": 1, "status": "native-sglang-rmsnorm-wave-entry-and-first-snapshot-checked",
        "local_lean_modules": 33, "library_axiom_audits": 260, "source_instances": 6,
        "source_axiom_audits_per_instance": 16, "false_lean_claims_rejected": len(controls),
        "axiom_audits": audits, "checks": checks,
        "source_archive_sha256": components.sha(out / "source.tar.gz"),
        "source_manifest_sha256": components.sha(out / "source-manifest.json"),
        "full_source_binding_proved": True, "native_wave_entry_success_proved": True,
        "native_warp_scheduler_prefix_transition_proved": True, "first_shuffle_executed_proved": True,
        "wave_threads": 64, "logical_partition_width": 32, "scalar_prefix_instructions_per_lane": 330,
        "snapshot_exit_pc": 45, "source_lane_fuel": 512, "source_warp_fuel": 8,
        "input_cache_cells_per_thread": 16, "weight_cache_cells_per_thread": 16, "new_access_events_per_wave": 5120,
        "private_cache_values_and_other_thread_state_framed": True,
        "arbitrary_prior_trace_preserved": True, "prior_trace_safety_assumed": False,
        "new_wave_trace_classified": True, "initial_wave_snapshot_race_freedom_proved": True,
        "all_five_first_reduction_shuffles_proved": False, "original_partial_store_reachability_proved": False,
        "first_block_barrier_reached_proved": False, "whole_kernel_execution_proved": False,
        "actual_whole_trace_classification_proved": False, "source_reference_equality_proved": False,
        "source_certificates": 0, "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: components.sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": 33, "audits": 356, "false_claims": len(controls)}), flush=True)


if __name__ == "__main__":
    main()
