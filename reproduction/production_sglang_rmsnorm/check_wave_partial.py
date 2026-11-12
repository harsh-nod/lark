"""Fresh complete native wave execution through its first block-barrier visit.

This proves all five first-reduction shuffles/adds and actual shared stores;
whole-block convergence, barrier resumption and whole-kernel correctness remain unproved.
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
TARGET = "Lark.NativeSglangRmsNormPartialEvents"


def statement(source, task, repaired):
    header = components.statement(source, task, repaired).split("theorem source_output_coverage", 1)[0]
    header = header.replace(components.TARGET, TARGET)
    text = header + r'''attribute [local irreducible] prefixFold reductionSnapshot partialFold
theorem source_wave_execution (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α)
    (hr : row<sourceShape.rows) (hw : warp<16)
    (hp : ∀ t∈cohortThreads row warp 64,s.pc t=0) (reads : Reads sourceShape input s) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) row warp) fuel.warp s =
      some (wavePartial sourceShape sourceRepaired ops input row warp s) := by
  rw [source_binding.1]
  exact native_wave_partial sourceShape sourceRepaired ops input row warp s hr hw hp reads
theorem source_initial_wave_execution (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<sourceShape.rows) (hw : warp<16) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) row warp) fuel.warp (initial sourceShape input outside) =
      some (wavePartial sourceShape sourceRepaired ops input row warp (initial sourceShape input outside)) := by
  rw [source_binding.1]
  exact initial_native_wave_partial sourceShape sourceRepaired ops input outside row warp hr hw
theorem source_all_five_reduction_values (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) :
    (wavePartial sourceShape sourceRepaired ops input row warp s).pc (cohortBase row warp+lane)=firstBarrier sourceRepaired ∧
    (wavePartial sourceShape sourceRepaired ops input row warp s).regs (cohortBase row warp+lane) 0=
      some (reductionValues ops (waveBaseValues ops input row warp) 5 lane) :=
  wave_partial_fields sourceShape sourceRepaired ops input row warp lane s hw hl
theorem source_first_barrier_site : sourceProgram[firstBarrier sourceRepaired]?=some (.scalar (.barrier .block)) := by
  rw [source_binding.1]
  exact first_barrier_code sourceRepaired
theorem source_private_caches (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) (reads : Reads sourceShape input s) :
    let t := cohortBase row warp+lane
    InputPrefix input row (warp*64+lane) 16 t (wavePartial sourceShape sourceRepaired ops input row warp s) ∧
    WeightPrefix input (warp*64+lane) 16 t (wavePartial sourceShape sourceRepaired ops input row warp s) :=
  wave_partial_caches sourceShape sourceRepaired ops input row warp lane s hw hl reads
theorem source_native_indices (ops : Ops α) (input : Nat → Nat → α) (row warp lane : Nat)
    (s : State α) (hl : lane<64) (reads : Reads sourceShape input s) :
    NativeIndices (cohortBase row warp+lane) (wavePartial sourceShape sourceRepaired ops input row warp s) :=
  wave_partial_native_indices sourceShape sourceRepaired ops input row warp lane s hl reads
theorem source_global_inputs (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (reads : Reads sourceShape input s) :
    Reads sourceShape input (wavePartial sourceShape sourceRepaired ops input row warp s) :=
  wave_partial_reads sourceShape sourceRepaired ops input row warp s reads
theorem source_epoch_frame (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (wavePartial sourceShape sourceRepaired ops input row warp s).epochs=s.epochs :=
  (wave_partial_indices_epochs sourceShape sourceRepaired ops input row warp s).2
theorem source_other_threads (ops : Ops α) (input : Nat → Nat → α) (row warp t : Nat)
    (s : State α) (ht : t∉cohortThreads row warp 64) :
    (wavePartial sourceShape sourceRepaired ops input row warp s).pc t=s.pc t ∧
    (wavePartial sourceShape sourceRepaired ops input row warp s).indices t=s.indices t ∧
    (wavePartial sourceShape sourceRepaired ops input row warp s).regs t=s.regs t :=
  wave_partial_other sourceShape sourceRepaired ops input row warp t s ht
theorem source_other_memory (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (l : Location)
    (hp : ∀ t∈cohortThreads row warp 64,OutsidePrivate t l)
    (hs : ∀ t∈cohortThreads row warp 64,l≠partialSlot t ((t%1024)/32)) :
    (wavePartial sourceShape sourceRepaired ops input row warp s).memory l=s.memory l :=
  wave_partial_memory sourceShape sourceRepaired ops input row warp s l hp hs
theorem source_exact_trace (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (wavePartial sourceShape sourceRepaired ops input row warp s).trace=
      partialEvents sourceRepaired s.epochs (cohortThreads row warp 64) ++ (wavePrepared ops input row warp s).trace :=
  wave_partial_trace sourceShape sourceRepaired ops input row warp s
theorem source_prior_trace (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (reads : Reads sourceShape input s) :
    ∃ events, (wavePartial sourceShape sourceRepaired ops input row warp s).trace=
      partialEvents sourceRepaired s.epochs (cohortThreads row warp 64) ++ events ++ s.trace ∧
      events.length=5120 ∧ (∀ event∈events,Good event) :=
  wave_partial_trace_tail sourceShape sourceRepaired ops input row warp s reads
theorem source_five_shuffle_sites :
    sourceProgram[44]?=some (.shuffle .xor 1 0 (.const 16) 32) ∧
    sourceProgram[46]?=some (.shuffle .xor 1 0 (.const 8) 32) ∧
    sourceProgram[48]?=some (.shuffle .xor 1 0 (.const 4) 32) ∧
    sourceProgram[50]?=some (.shuffle .xor 1 0 (.const 2) 32) ∧
    sourceProgram[52]?=some (.shuffle .xor 1 0 (.const 1) 32) ∧
    sourceProgram[53]?=some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  rw [source_binding.1]
  decide
'''
    race = "initial_fixed_wave_partial_race_free sourceShape ops input outside row warp" if repaired else "initial_original_wave_partial_racy sourceShape ops input outside row warp hw"
    text += "theorem source_actual_race_classification (ops : Ops α) (input : Nat → Nat → α)\n    (outside : Location → Option α) (row warp : Nat) (hw : warp<16) :\n    raceFree (geometry sourceShape) (wavePartial sourceShape sourceRepaired ops input row warp (initial sourceShape input outside)).trace=sourceRepaired :=\n  " + race + "\n"
    text += r'''theorem source_execution_and_classification (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<sourceShape.rows) (hw : warp<16) :
    ∃ final, LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) row warp) fuel.warp (initial sourceShape input outside)=some final ∧
      raceFree (geometry sourceShape) final.trace=sourceRepaired :=
  ⟨wavePartial sourceShape sourceRepaired ops input row warp (initial sourceShape input outside),
    source_initial_wave_execution ops input outside row warp hr hw,
    source_actual_race_classification ops input outside row warp hw⟩
theorem source_fixed_leader_events (epochs : Nat → Epoch) (row warp : Nat) (hw : warp<16)
    (repaired : sourceRepaired=true) :
    partialEvents sourceRepaired epochs (cohortThreads row warp 64)=
      [partialAccess epochs (cohortBase row warp+32),partialAccess epochs (cohortBase row warp)] := by
  rw [repaired]
  exact fixed_wave_events epochs row warp hw
theorem source_original_access_member (epochs : Nat → Epoch) (row warp lane : Nat) (hl : lane<64)
    (original : sourceRepaired=false) :
    ⟨cohortBase row warp+lane,partialSlot (cohortBase row warp+lane) (((cohortBase row warp+lane)%1024)/32),true,epochs (cohortBase row warp+lane)⟩∈
      partialEvents sourceRepaired epochs (cohortThreads row warp 64) := by
  rw [original]
  exact original_partial_events_member epochs _ _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)
theorem source_shared_location (epochs : Nat → Epoch) (row warp lane : Nat) (hw : warp<16) (hl : lane<64) :
    (partialAccess epochs (cohortBase row warp+lane)).location=⟨.shared,row,0,warp*2+lane/32⟩ :=
  partial_access_location epochs row warp lane hw hl
'''
    if repaired:
        text += "theorem source_exact_event_count (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)\n    (s : State α) (hw : warp<16) :\n    (wavePartial sourceShape sourceRepaired ops input row warp s).trace.length=s.trace.length+5122 :=\n  fixed_wave_partial_trace_length sourceShape ops input row warp s hw\n"
    else:
        text += "theorem source_exact_event_count (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)\n    (s : State α) (hw : warp<16) :\n    (wavePartial sourceShape sourceRepaired ops input row warp s).trace.length=s.trace.length+5184 :=\n  original_wave_partial_trace_length sourceShape ops input row warp s\n"
    names = ['source_binding','source_wave_execution','source_initial_wave_execution','source_all_five_reduction_values','source_first_barrier_site','source_private_caches','source_native_indices','source_global_inputs','source_epoch_frame','source_other_threads','source_other_memory','source_exact_trace','source_prior_trace','source_five_shuffle_sites','source_actual_race_classification','source_execution_and_classification','source_fixed_leader_events','source_original_access_member','source_shared_location','source_exact_event_count']
    assert len(names) == 20
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
    if len(own) != 43 or sum(s.count("#print axioms ") for s in own.values()) != 346:
        raise ValueError("Unexpected native wave/store closure")
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

    run("fresh-build", [lake, "build", TARGET], count=346)
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
            run(name, [lake, "env", "lean", name + ".lean"], count=20)
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
        "wrong-last-shuffle": text.replace("__shfl_xor(sum, 1, 32)", "__shfl_xor(sum, 2, 32)", 1),
        "wrong-leader-predicate": text.replace("if (lane == 0)", "if (lane == 1)", 1),
        "wrong-shared-slot": text.replace("partial[warp] = sum;", "partial[lane] = sum;", 1),
        "missing-first-barrier": text.replace("__syncthreads();", "", 1),
    }
    controls = {name: statement(changed, task, True) for name, changed in changes.items() if changed != text}
    if len(controls) != 10:
        raise ValueError("Unchanged native source control")
    header = f'''import {TARGET}
open LarkNonlinear LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold
def p : Shape := ⟨1,by decide,by decide⟩
def ops : Ops Nat := ⟨fun i _ => i.toNat,Nat.add,Nat.sub,Nat.mul,Nat.max,Nat.div,id,id,id,id,id⟩
def input (_ i : Nat) := i
def base := initial p input (fun _ => none)
def prior : State Nat := {{base with trace := [⟨999,globalCell 0 0,true,{{}}⟩]}}
'''
    controls["crossed-logical-partition"] = header + "example : xorPeer32 31 16 = 47 := by decide\n"
    controls["erased-prior-trace"] = header + '''example : (wavePartial p true ops input 0 0 prior).trace.length=5122 := by
  rw [fixed_wave_partial_trace_length p ops input 0 0 prior (by decide)]
  decide
'''
    controls["invented-barrier-resume"] = header + '''example : ((wavePartial p true ops input 0 0 base).epochs 0).block=1 := by
  rw [(wave_partial_indices_epochs p true ops input 0 0 base).2]
  decide
'''
    controls["invented-whole-kernel-pc"] = header + '''example : (wavePartial p true ops input 0 0 base).pc 0=109 := by
  have h := (wave_partial_fields p true ops input 0 0 0 base (by decide) (by decide)).1
  have hpc : (wavePartial p true ops input 0 0 base).pc 0=56 := by
    simpa only [cohortBase,Nat.zero_mul,Nat.zero_add,Nat.add_zero,firstBarrier] using h
  rw [hpc]
  decide
'''
    controls["invented-original-race-freedom"] = header + '''example : raceFree (geometry p) (wavePartial p false ops input 0 0 base).trace=true := by
  change raceFree (geometry p) (wavePartial p false ops input 0 0 (initial p input (fun _ => none))).trace=true
  rw [initial_original_wave_partial_racy p ops input (fun _ => none) 0 0 (by decide)]
  decide
'''
    controls["invented-repaired-race"] = header + '''example : raceFree (geometry p) (wavePartial p true ops input 0 0 base).trace=false := by
  change raceFree (geometry p) (wavePartial p true ops input 0 0 (initial p input (fun _ => none))).trace=false
  rw [initial_fixed_wave_partial_race_free p ops input (fun _ => none) 0 0]
  decide
'''
    controls["erased-original-writes"] = header + '''example : (partialEvents false base.epochs (cohortThreads 0 0 64)).length=2 := by
  rw [original_partial_events_length]
  decide
'''
    controls["invented-repaired-writes"] = header + '''example : (partialEvents true base.epochs (cohortThreads 0 0 64)).length=64 := by
  rw [fixed_wave_events base.epochs 0 0 (by decide)]
  decide
'''
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {
        "schema": 1, "status": "native-sglang-rmsnorm-wave-first-barrier-and-initialized-race-checked",
        "local_lean_modules": 43, "library_axiom_audits": 346, "source_instances": 6,
        "source_axiom_audits_per_instance": 20, "false_lean_claims_rejected": len(controls),
        "axiom_audits": audits, "checks": checks,
        "source_archive_sha256": components.sha(out / "source.tar.gz"),
        "source_manifest_sha256": components.sha(out / "source-manifest.json"),
        "full_source_binding_proved": True, "native_wave_first_barrier_execution_proved": True,
        "all_five_first_reduction_shuffles_proved": True, "all_five_first_reduction_additions_proved": True,
        "original_partial_store_reachability_proved": True, "repaired_partial_stores_proved": True,
        "original_initialized_wave_racy_proved": True, "repaired_initialized_wave_race_freedom_proved": True,
        "wave_threads": 64, "logical_partition_width": 32, "source_lane_fuel": 512, "source_warp_fuel": 8,
        "original_exit_pc": 55, "repaired_exit_pc": 56,
        "input_cache_cells_per_thread": 16, "weight_cache_cells_per_thread": 16,
        "new_private_events_per_wave": 5120, "original_partial_writes_per_wave": 64, "repaired_partial_writes_per_wave": 2,
        "original_new_events_per_wave": 5184, "repaired_new_events_per_wave": 5122,
        "private_cache_values_and_other_thread_state_framed": True,
        "arbitrary_prior_trace_preserved": True, "prior_trace_safety_assumed": False,
        "epochs_preserved_at_barrier_visit": True,
        "whole_block_barrier_convergence_proved": False, "first_block_barrier_resumed_proved": False,
        "whole_kernel_execution_proved": False, "actual_whole_trace_classification_proved": False,
        "source_reference_equality_proved": False, "source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: components.sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": 43, "audits": 466, "false_claims": len(controls)}), flush=True)


if __name__ == "__main__":
    main()
