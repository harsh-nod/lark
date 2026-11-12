"""Rebuild both SGLang sources, addresses, private caches and cut-state witnesses.

The packet does not prove that the initializer reaches the instruction cut state.
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import collective, native_sglang_rmsnorm as native
from lark_kernels.ir import lean_list

HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeSglangRmsNormWitness"
ROWS = (1, 3, 131072)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modules(name, found):
    if name in found:
        return
    source = (ROOT / "lean" / (name.replace(".", "/") + ".lean")).read_text()
    found[name] = source
    for line in source.splitlines():
        if line.startswith("import "):
            for imported in line.split()[1:]:
                if imported.startswith("Lark."):
                    modules(imported, found)
                elif imported != "Std":
                    raise ValueError("Unexpected external import")


def statement(source, task, repaired):
    tr = native.translate(source, task)
    return f'''import {TARGET}
open LarkNonlinear LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩
def sourceProgram : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
def sourceGlobal : List Buffer := {lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}
def sourceShared : List Nat := {[n for _, n in tr.shared]}
def sourcePrivate : List Nat := {[n for _, n in tr.locals]}
def sourceRepaired : Bool := {str(repaired).lower()}
def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩
def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩
theorem source_binding : sourceProgram = program sourceRepaired ∧
    sourceGlobal = (layout sourceShape).global ∧ sourceShared = (layout sourceShape).shared ∧
    sourcePrivate = (layout sourceShape).locals ∧
    sourceGeometry = geometry sourceShape ∧ sourceFuel = fuel := by decide
theorem source_output_coverage (col : Nat) (hc : col < 16384) :
    ∃ tid < 1024, ∃ iteration < 2, ∃ component < 8, column tid iteration component = col := coverage col hc
theorem source_native_writer (row tid iteration component : Nat)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    writer (address row (column tid iteration component)) = row * 1024 + tid :=
  address_writer row tid iteration component ht hi hc
theorem source_signed_bounds (row tid iteration component : Nat)
    (hr : row < sourceShape.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    address row (column tid iteration component) < 2147483648 :=
  address_int32 sourceShape row tid iteration component hr ht hi hc
theorem source_conditional_race_free (trace : List Access) (good : ∀ a ∈ trace, Good a) :
    raceFree (geometry sourceShape) trace = true := race_free sourceShape trace good
theorem source_private_pair_bounds (iteration pair : Nat) (hi : iteration < 2) (hp : pair < 4) :
    iteration * 8 + pair * 2 < 16 ∧ iteration * 8 + pair * 2 + 1 < 16 := private_pair_bound iteration pair hi hp
theorem source_private_location (t buffer offset : Nat) (write : Bool) (hb : buffer < 3) (ho : offset < 16) :
    location (layout sourceShape) (geometry sourceShape) t .local buffer (offset : Int) write =
      some ⟨.local,t,buffer,offset⟩ := private_location sourceShape t buffer offset write hb ho
theorem source_original_cut_execution (ops : Ops α) (value : α) :
    ((execute ops (layout sourceShape) (geometry sourceShape) 0 (.store .shared 0 (.ivar 3) (.reg 0))
      (cutState value)).bind fun s =>
        execute ops (layout sourceShape) (geometry sourceShape) 1 (.store .shared 0 (.ivar 3) (.reg 0)) s) =
      some (originalPair value) := original_pair_exec sourceShape ops value
theorem source_original_cut_racy (value : α) :
    raceFree (geometry sourceShape) (originalPair value).trace = false := original_pair_racy sourceShape value
theorem source_guarded_cut_execution (ops : Ops α) (value : α) :
    ((execute ops (layout sourceShape) (geometry sourceShape) 0 (.branch (.eq (.ivar 2) (.const 0)) 56)
      (cutState value)).bind fun s =>
        (execute ops (layout sourceShape) (geometry sourceShape) 0 (.store .shared 0 (.ivar 3) (.reg 0)) s).bind fun s =>
          execute ops (layout sourceShape) (geometry sourceShape) 1 (.branch (.eq (.ivar 2) (.const 0)) 56) s) =
      some (guardedPair value) := guarded_pair_exec sourceShape ops value
theorem source_guarded_cut_race_free (value : α) :
    raceFree (geometry sourceShape) (guardedPair value).trace = true := guarded_pair_race_free sourceShape value
#print axioms source_private_pair_bounds
#print axioms source_private_location
#print axioms source_original_cut_execution
#print axioms source_original_cut_racy
#print axioms source_guarded_cut_execution
#print axioms source_guarded_cut_race_free
#print axioms source_binding
#print axioms source_output_coverage
#print axioms source_native_writer
#print axioms source_signed_bounds
#print axioms source_conditional_race_free
'''


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
    modules(TARGET, own)
    source = out / "source"
    files = ["lean/" + name.replace(".", "/") + ".lean" for name in own]
    files += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    files += [str(p.relative_to(ROOT)) for p in (ROOT / "lark_kernels").glob("*.py")]
    files += [str(p.relative_to(ROOT)) for p in HERE.glob("*.py")]
    files += [str(p.relative_to(ROOT)) for folder in ("cases", "upstream")
              for p in (HERE / folder).rglob("*") if p.is_file()]
    files += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for name in sorted(set(files)):
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, dest)
        hashes[name] = sha(dest)
    (out / "source-manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in hashes:
            archive.add(source / name, arcname=name, recursive=False)
    checks, audits = [], {}
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)

    def run(name, command, *, accepted=True, count=None):
        start = time.monotonic()
        result = subprocess.run(command, cwd=source / "lean", env=env,
                                capture_output=True, text=True, timeout=180)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        if (result.returncode == 0) is not accepted:
            raise ValueError("Unexpected Lean result: " + name + ": " + log)
        if accepted:
            entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
            found = {k: [a.strip() for a in v.split(",") if a.strip()] for k, v in entries}
            if (len(entries) != len(found) or len(found) != count
                    or any(not set(v) <= {"propext", "Classical.choice", "Quot.sound"} for v in found.values())):
                raise ValueError("Axiom closure differs: " + name)
            audits[name] = found
        elif ("is false" not in log
              or re.search(r"maximum recursion|heartbeats|stack overflow|timed out|out of memory", log, re.I)):
            raise ValueError("Changed claim did not fail logically: " + name)
        checks.append({"name": name, "accepted": accepted, "exit_code": result.returncode,
                       "seconds": time.monotonic() - start})

    if len(own) != 7 or sum(text.count("#print axioms ") for text in own.values()) != 36:
        raise ValueError("Unexpected component proof closure")
    run("fresh-build", [lake, "build", TARGET], count=36)
    for variant, repaired in (("native_original", False), ("native_fixed", True)):
        case = HERE / "cases" / variant
        text = (case / "kernel.hip").read_text()
        native.check_reference((case / "reference.py").read_text())
        for rows in ROWS:
            data = json.loads((case / "task.json").read_text())
            data["launch"]["grid"] = rows
            data["buffers"][0]["shape"][0] = data["buffers"][1]["shape"][0] = rows
            task = native.parse_task(json.dumps(data))
            name = variant + "_rows_" + str(rows)
            (source / "lean" / (name + ".lean")).write_text(statement(text, task, repaired))
            run(name, [lake, "env", "lean", name + ".lean"], count=11)
    case = HERE / "cases/native_fixed"
    text = (case / "kernel.hip").read_text()
    task = native.parse_task((case / "task.json").read_text())
    first, last = text.rsplit("__syncthreads();", 1)
    changes = {
        "wrong-reduction-mask": text.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 8, 32)", 1),
        "wrong-logical-width": text.replace("__shfl_xor(sum, 16, 32)", "__shfl_xor(sum, 16, 64)", 1),
        "removed-first-barrier": text.replace("__syncthreads();", "", 1),
        "removed-second-barrier": first + last,
        "wrong-inverse-slot": text.replace("float inverse = partial[warp];", "float inverse = partial[0];"),
        "aliased-output": text.replace("output[store_address]", "output[row * 16384]"),
        "wrong-pair-grouping": text.replace("sum = sum + pair_square;", "sum = (sum + xx) + yy;"),
        "unguarded-repair": text.replace("if (lane == 0) {\npartial[warp] = sum;\n}", "partial[warp] = sum;", 1),
    }
    controls = {}
    for name, changed in changes.items():
        if text == changed:
            raise ValueError("Unchanged negative source: " + name)
        controls[name] = statement(changed, task, True)
    controls["denied-output-owner"] = '''import Lark.NativeSglangRmsNormWitness
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : writer (address 0 (column 17 1 3)) ≠ 17 := by decide
'''
    controls["wrong-private-layout"] = statement(text, task, True).replace(
        "def sourcePrivate : List Nat := [16, 16, 16]", "def sourcePrivate : List Nat := [8, 16, 16]", 1)
    controls["invented-original-race-freedom"] = '''import Lark.NativeSglangRmsNormWitness
open LarkNonlinear LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : raceFree (geometry ⟨1,by decide,by decide⟩) (originalPair (0 : Nat)).trace = true := by decide
'''
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {
        "schema": 1, "status": "native-sglang-rmsnorm-source-private-and-cut-components-checked",
        "local_lean_modules": len(own), "library_axiom_audits": 36,
        "source_instances": 2 * len(ROWS), "source_axiom_audits_per_instance": 11,
        "false_lean_claims_rejected": len(controls), "axiom_audits": audits, "checks": checks,
        "source_archive_sha256": sha(out / "source.tar.gz"),
        "source_manifest_sha256": sha(out / "source-manifest.json"),
        "full_source_binding_proved": True, "address_coverage_and_native_ownership_proved": True,
        "conditional_footprint_race_freedom_proved": True,
        "private_cache_bounds_and_owner_proved": True, "cut_state_store_pair_executed": True,
        "cut_state_original_write_conflict_proved": True, "cut_state_guarded_tail_race_freedom_proved": True,
        "initializer_reaches_cut_state_proved": False,
        "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
        "source_reference_equality_proved": False, "source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir())
                                                  if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(own), "audits": 102,
                      "source_instances": 2 * len(ROWS), "false_claims": len(controls)}), flush=True)


if __name__ == "__main__":
    main()
