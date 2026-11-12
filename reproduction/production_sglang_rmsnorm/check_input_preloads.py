"""Fresh source-bound scalar prefix equations through the input caches at PC16.

The first-shuffle continuation and complete launch are not established here.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

import check_program as components

ROOT, HERE = components.ROOT, components.HERE
TARGET = "Lark.NativeSglangRmsNormInputPreloads"


def statement(source, task, repaired):
    header = components.statement(source, task, repaired).split("theorem source_output_coverage", 1)[0]
    header = header.replace(components.TARGET, TARGET)
    text = header + '''theorem source_preload_equation (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t extra : Nat) (ht : t < sourceShape.rows * 1024) :
    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t
      (extra + 128) (initial sourceShape input outside) =
    LarkCollective.runLane ops (layout sourceShape) (geometry sourceShape) sourceProgram t extra
      (inputPreloads input t (initial sourceShape input outside)) := by
  rw [source_binding.1]
  exact initial_input_preloads_eq sourceShape sourceRepaired ops input outside t extra ht
theorem source_cached_values (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :
    InputPrefix input (t / 1024) (t % 1024) 16 t (inputPreloads input t (initial sourceShape input outside)) :=
  initial_input_preloads_values sourceShape input outside t
theorem source_readonly_globals (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :
    Reads sourceShape input (inputPreloads input t (initial sourceShape input outside)) :=
  initial_input_preloads_reads sourceShape input outside t
theorem source_preload_footprint (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (inputPreloads input t (initial sourceShape input outside)).trace, Good a :=
  initial_input_preloads_good sourceShape input outside t
theorem source_preload_race_free (input : Nat → Nat → α) (outside : Location → Option α) (t : Nat) :
    raceFree (geometry sourceShape) (inputPreloads input t (initial sourceShape input outside)).trace = true :=
  initial_input_preloads_race_free sourceShape input outside t
theorem source_preload_pc (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).pc t = 16 := input_preloads_pc input t s
theorem source_preload_epochs (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).epochs = s.epochs := input_preloads_epochs input t s
theorem source_preload_trace_length (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).trace.length = s.trace.length + 32 := input_preloads_trace_length input t s
theorem source_private_bounds (iteration component : Nat) (hi : iteration < 2) (hc : component < 8) :
    iteration * 8 + component < 16 := private_slot_bound iteration component hi hc
'''
    names = ["source_binding", "source_preload_equation", "source_cached_values", "source_readonly_globals",
             "source_preload_footprint", "source_preload_race_free", "source_preload_pc",
             "source_preload_epochs", "source_preload_trace_length", "source_private_bounds"]
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
    if len(own) != 14 or sum(s.count("#print axioms ") for s in own.values()) != 80:
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

    run("fresh-build", [lake, "build", TARGET], count=80)
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
            run(name, [lake, "env", "lean", name + ".lean"], count=10)
    case = HERE / "cases/native_fixed"
    text = (case / "kernel.hip").read_text()
    task = components.native.parse_task((case / "task.json").read_text())
    changes = {
        "aliased-input-cache-slot": text.replace("input_values[input_slot] =", "input_values[0] =", 1),
        "wrong-input-cache-address": text.replace("input[input_address]", "input[input_column]", 1),
    }
    controls = {name: statement(changed, task, True) for name, changed in changes.items() if changed != text}
    if len(controls) != 2:
        raise ValueError("Unchanged cache source control")
    header = f'''import {TARGET}
open LarkNonlinear LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def p : Shape := ⟨1,by decide,by decide⟩
def s := inputPreloads (fun _ i => i) 0 (initial p (fun _ i => i) (fun _ => none))
'''
    for name, claim in {
        "invented-weight-preload-pc": "s.pc 0 = 27",
        "missing-private-write-events": "s.trace.length = 16",
        "wrong-last-input-half": "s.memory (privateCell 0 0 15) = some 0",
        "invented-weight-cache-value": "s.memory (privateCell 0 1 0) = some 0",
    }.items():
        controls[name] = header + "example : " + claim + " := by decide\n"
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {
        "schema": 1, "status": "native-sglang-rmsnorm-input-preload-prefix-equations-checked",
        "local_lean_modules": 14, "library_axiom_audits": 80, "source_instances": 6,
        "source_axiom_audits_per_instance": 10, "false_lean_claims_rejected": len(controls),
        "axiom_audits": audits, "checks": checks,
        "source_archive_sha256": components.sha(out / "source.tar.gz"),
        "source_manifest_sha256": components.sha(out / "source-manifest.json"),
        "full_source_binding_proved": True, "input_preload_prefix_equation_proved": True,
        "prefix_instruction_count": 128, "prefix_exit_pc": 16, "input_cache_cells": 16,
        "prefix_access_events": 32, "private_cache_values_and_readonly_globals_proved": True,
        "initializer_reaches_partial_store_cut_proved": False, "continued_lane_success_proved": False,
        "whole_kernel_execution_proved": False, "actual_whole_trace_classification_proved": False,
        "source_reference_equality_proved": False, "source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: components.sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": 14, "audits": 140, "false_claims": len(controls)}), flush=True)


if __name__ == "__main__":
    main()
