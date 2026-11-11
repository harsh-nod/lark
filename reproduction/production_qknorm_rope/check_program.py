"""Fresh full-source binding and native address/ownership component checks.

Complete execution, actual trace classification and dense reference equality
are not claimed by this development packet.
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
from lark_kernels import collective, native_qknorm_rope as native
from lark_kernels.ir import lean_list

HERE = Path(__file__).resolve().parent
TARGET = "Lark.NativeQKNormRopeAddress"


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


def statement(source, contract):
    tr, task = native.translate(source, contract), contract.task
    neox = str(contract.rotary_layout == "split-half").lower()
    return f'''import {TARGET}
open LarkNonlinear LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def sourceShape : Shape := ⟨{contract.rows}, by decide, by decide⟩
def sourceNeox : Bool := {neox}
def sourceProgram : List LarkCollective.Instr := {lean_list(collective.emit(i) for i in tr.program)}
def sourceGlobal : List Buffer := {lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}
def sourceShared : List Nat := {[v for _, v in tr.shared]}
def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩
def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩
theorem source_binding : sourceProgram = program sourceNeox ∧
    sourceGlobal = (layout sourceShape).global ∧ sourceShared = (layout sourceShape).shared ∧
    sourceGeometry = geometry sourceShape ∧ sourceFuel = fuel := by decide
theorem source_pre_satisfiable (input : Nat → Nat → α) :
    ∃ s, StdPre (layout sourceShape) input s := pre_satisfiable _ input
theorem source_native_head (t : Nat) : t / 256 * 8 + t % 256 / 32 = t / 32 := native_head t
theorem source_output_coverage (i : Nat) (hi : i < sourceShape.rows * 5120) :
    ∃ t < sourceShape.rows * 1280, ∃ e < 4, outputAddress t e = i := output_coverage sourceShape i hi
theorem source_native_writer (t e : Nat) (he : e < 4) : outputAddress t e / 4 = t := output_owner t e he
theorem source_input_bound (t e : Nat) (ht : t < sourceShape.rows * 1280) (he : e < 4) :
    inputAddress t e < sourceShape.rows * 6144 := input_bound sourceShape t e ht he
theorem source_never_v (t e : Nat) (he : e < 4) :
    row t * 6144 ≤ inputAddress t e ∧ inputAddress t e < row t * 6144 + 5120 := input_never_v t e he
theorem source_signed_bounds (t e : Nat) (ht : t < sourceShape.rows * 1280) (he : e < 4) :
    inputAddress t e < 2147483648 ∧ outputAddress t e < 2147483648 := signed_bounds sourceShape t e ht he
theorem source_conditional_race_free (trace : List Access) (good : ∀ a ∈ trace, Good a) :
    raceFree (geometry sourceShape) trace = true := race_free sourceShape trace good
#print axioms source_binding
#print axioms source_pre_satisfiable
#print axioms source_native_head
#print axioms source_output_coverage
#print axioms source_native_writer
#print axioms source_input_bound
#print axioms source_never_v
#print axioms source_signed_bounds
#print axioms source_conditional_race_free
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh standalone output outside repository required")
    out.mkdir(parents=True, exist_ok=False)
    lake = str(args.lean_bin / "lake") if args.lean_bin else shutil.which("lake")
    if not lake or "Lean version 4.19.0" not in subprocess.check_output([lake, "--version"], text=True):
        raise ValueError("Pinned Lean/Lake4.19.0 required")
    own = {}
    modules(TARGET, own)
    source = out / "source"
    files = ["lean/" + n.replace(".", "/") + ".lean" for n in own]
    files += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    files += [str(p.relative_to(ROOT)) for p in (ROOT / "lark_kernels").glob("*.py")]
    files += [str(p.relative_to(ROOT)) for p in HERE.glob("*.py")]
    files += [str(p.relative_to(ROOT)) for folder in ("cases", "upstream") for p in (HERE / folder).rglob("*") if p.is_file()]
    files += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for filename in sorted(set(files)):
        dest = source / filename
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / filename, dest)
        hashes[filename] = sha(dest)
    (out / "source-manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for filename in hashes:
            archive.add(source / filename, arcname=filename, recursive=False)
    checks, audits = [], {}
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)

    def run(name, command, *, accepted=True, count=None):
        start = time.monotonic()
        result = subprocess.run(command, cwd=source / "lean", env=env, capture_output=True, text=True, timeout=180)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        if (result.returncode == 0) is not accepted:
            raise ValueError("Unexpected Lean result: " + name + ": " + log)
        if accepted:
            entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
            found = {k: [a.strip() for a in v.split(",") if a.strip()] for k, v in entries}
            if len(entries) != len(found) or len(found) != count or any(not set(v) <= {"propext", "Classical.choice", "Quot.sound"} for v in found.values()):
                raise ValueError("Axiom closure differs: " + name)
            audits[name] = found
        elif "is false" not in log or re.search(r"maximum recursion|heartbeats|stack overflow|timed out|out of memory", log, re.I):
            raise ValueError("Changed claim did not fail logically: " + name)
        checks.append({"name": name, "accepted": accepted, "exit_code": result.returncode, "seconds": time.monotonic() - start})

    run("fresh-build", [lake, "build", TARGET], count=31)
    contracts = {}
    for layout in native.LAYOUTS:
        case = HERE / "cases" / layout
        for rows in (1, 3, 256, 65535):
            raw = json.loads((case / "task.json").read_text())
            raw["launch"]["grid"] = rows * 5
            for b in raw["buffers"]:
                if len(b["shape"]) > 1:
                    b["shape"][0] = rows
            contract = native.parse_task(json.dumps(raw))
            native.check_reference((case / "reference.py").read_text(), layout)
            text = (case / "kernel.hip").read_text()
            name = layout.replace("-", "_") + "_" + str(rows)
            (source / "lean" / (name + ".lean")).write_text(statement(text, contract))
            run(name, [lake, "env", "lean", name + ".lean"], count=9)
            if rows == 1:
                contracts[layout] = text, contract
    text, contract = contracts["interleaved"]
    changes = {
        "wrong-reduction-mask": text.replace("peer = __shfl_xor(ss, 16, 32);", "peer = __shfl_xor(ss, 8, 32);"),
        "wrong-logical-width": text.replace("peer = __shfl_xor(ss, 16, 32);", "peer = __shfl_xor(ss, 16, 16);"),
        "wrong-cache-half": text.replace("int sa0 = ca0 + 64;", "int sa0 = ca0 + 63;"),
        "wrong-key-weight": text.replace("weight0 = __half2float(k_weight[w0]);", "weight0 = __half2float(q_weight[w0]);"),
        "missing-store": text.replace("  output[out3] = __float2half(o3);\n", ""),
        "missing-normalization": text.replace("float n0 = x0 * scaledWeight0;", "float n0 = x0;"),
        "wrong-input-row-stride": text.replace("row * 6144", "row * 5120"),
        "wrong-layout-label": contracts["split-half"][0],
    }
    controls = {name: statement(changed, contract) for name, changed in changes.items()}
    controls["denied-output-owner"] = "import Lark.NativeQKNormRopeAddress\nopen LarkNativeQKNormRope\nexample : outputAddress 17 3 / 4 ≠ 17 := by decide\n"
    for name, contents in controls.items():
        filename = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / filename).write_text(contents)
        run(name, [lake, "env", "lean", filename], accepted=False)
    report = {"schema": 1, "status": "native-fused-qknorm-rope-full-source-and-ownership-components-checked",
              "local_lean_modules": len(own), "library_axiom_audits": 31, "source_instances": 8,
              "source_axiom_audits_per_instance": 9, "false_lean_claims_rejected": len(controls),
              "axiom_audits": audits, "checks": checks, "source_archive_sha256": sha(out / "source.tar.gz"),
              "source_manifest_sha256": sha(out / "source-manifest.json"), "full_source_binding_proved": True,
              "address_coverage_and_native_ownership_proved": True, "conditional_footprint_race_freedom_proved": True,
              "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
              "source_reference_equality_proved": False, "source_certificates": 0, "model_calls": 0,
              "gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(own), "audits": 103, "false_claims": len(controls)}))


if __name__ == "__main__":
    main()
