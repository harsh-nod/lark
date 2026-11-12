"""Fresh complete scalar preparation to the first native SGLang shuffle at PC44.

The first shuffle is reached; no shuffle, barrier, shared store or complete launch is proved here.
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
TARGET = "Lark.NativeSglangRmsNormPrefix"


def statement(source, task, repaired):
    header = components.statement(source, task, repaired).split("theorem source_output_coverage", 1)[0]
    header = header.replace(components.TARGET, TARGET)
    text = header + 'theorem source_prefix_success (ops : Ops α) (input : Nat → Nat → α)\n    (outside : Location → Option α) (t : Nat) (ht : t < sourceShape.rows * 1024) :\n    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t fuel.lane\n      (initial sourceShape input outside) = some (prefixState ops input t (initial sourceShape input outside)) := by\n  rw [source_binding.1]\n  exact initial_prefix_run sourceShape sourceRepaired ops input outside t ht\ntheorem source_prefix_equation (ops : Ops α) (input : Nat → Nat → α)\n    (outside : Location → Option α) (t extra : Nat) (ht : t < sourceShape.rows * 1024) :\n    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t\n      (extra + 330) (initial sourceShape input outside) =\n    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t extra\n      (prefixState ops input t (initial sourceShape input outside)) := by\n  rw [source_binding.1]\n  exact initial_prefix_eq sourceShape sourceRepaired ops input outside t extra ht\ntheorem source_sum_and_caches (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :\n    (prefixState ops input t (initial sourceShape input outside)).regs t 0 =\n      some (threadSum ops input (t / 1024) (t % 1024)) ∧\n    InputPrefix input (t / 1024) (t % 1024) 16 t (prefixState ops input t (initial sourceShape input outside)) ∧\n    WeightPrefix input (t % 1024) 16 t (prefixState ops input t (initial sourceShape input outside)) :=\n  initial_prefix_values sourceShape ops input outside t\ntheorem source_readonly_globals (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :\n    Reads sourceShape input (prefixState ops input t (initial sourceShape input outside)) :=\n  initial_prefix_reads sourceShape ops input outside t\ntheorem source_actual_prefix_footprint (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :\n    ∀ a ∈ (prefixState ops input t (initial sourceShape input outside)).trace, Good a :=\n  initial_prefix_good sourceShape ops input outside t\ntheorem source_actual_prefix_race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :\n    raceFree (geometry sourceShape) (prefixState ops input t (initial sourceShape input outside)).trace = true :=\n  initial_prefix_race_free sourceShape ops input outside t\ntheorem source_prefix_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :\n    (prefixState ops input t s).pc t = 44 := prefix_pc ops input t s\ntheorem source_prefix_epochs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :\n    (prefixState ops input t s).epochs = s.epochs := prefix_epochs ops input t s\ntheorem source_prefix_trace_length (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :\n    (prefixState ops input t s).trace.length = s.trace.length + 80 := prefix_trace_length ops input t s\ntheorem source_private_bounds (iteration component : Nat) (hi : iteration < 2) (hc : component < 8) :\n    iteration * 8 + component < 16 := private_slot_bound iteration component hi hc\ntheorem source_first_shuffle : sourceProgram[44]? = some (.shuffle .xor 1 0 (.const 16) 32) := by\n  rw [source_binding.1]\n  decide\n'
    names = ["source_binding", "source_prefix_success", "source_prefix_equation", "source_sum_and_caches",
             "source_readonly_globals", "source_actual_prefix_footprint", "source_actual_prefix_race_free",
             "source_prefix_pc", "source_prefix_epochs", "source_prefix_trace_length", "source_private_bounds",
             "source_first_shuffle"]
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
    if len(own) != 23 or sum(s.count("#print axioms ") for s in own.values()) != 152:
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
        result = subprocess.run(command, cwd=source / "lean", env=env, capture_output=True, text=True, timeout=180)
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

    run("fresh-build", [lake, "build", TARGET], count=152)
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
            run(name, [lake, "env", "lean", name + ".lean"], count=12)
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
def p : Shape := ⟨1,by decide,by decide⟩
def ops : Ops Nat := ⟨fun i _ => i.toNat,Nat.add,Nat.sub,Nat.mul,Nat.max,Nat.div,id,id,id,id,id⟩
def s := prefixState ops (fun _ i => i) 0 (initial p (fun _ i => i) (fun _ => none))
'''
    for name, claim in {
        "invented-partial-store-pc": "s.pc 0 = 54",
        "missing-private-read-events": "s.trace.length = 64",
        "invented-block-barrier": "(s.epochs 0).block = 1",
        "wrong-last-weight-half": "s.memory (privateCell 0 1 15) = some 0",
    }.items():
        controls[name] = header + "example : " + claim + " := by decide\n"
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {
        "schema": 1, "status": "native-sglang-rmsnorm-successful-first-shuffle-prefix-checked",
        "local_lean_modules": 23, "library_axiom_audits": 152, "source_instances": 6,
        "source_axiom_audits_per_instance": 12, "false_lean_claims_rejected": len(controls),
        "axiom_audits": audits, "checks": checks,
        "source_archive_sha256": components.sha(out / "source.tar.gz"),
        "source_manifest_sha256": components.sha(out / "source-manifest.json"),
        "full_source_binding_proved": True, "first_shuffle_reached_proved": True,
        "input_weight_preloads_and_paired_squares_proved": True,
        "prefix_instruction_count": 330, "prefix_exit_pc": 44, "source_lane_fuel": 512,
        "input_cache_cells": 16, "weight_cache_cells": 16, "prefix_access_events": 80,
        "private_cache_values_and_readonly_globals_proved": True,
        "actual_prefix_trace_classification_proved": True, "actual_prefix_race_freedom_proved": True,
        "initializer_reaches_partial_store_cut_proved": False,
        "first_block_barrier_reached_proved": False, "whole_kernel_execution_proved": False,
        "actual_whole_trace_classification_proved": False, "source_reference_equality_proved": False,
        "source_certificates": 0, "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: components.sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": 23, "audits": 224, "false_claims": len(controls)}), flush=True)


if __name__ == "__main__":
    main()
