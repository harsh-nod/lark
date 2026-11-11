"""Fresh source binding, initialized interface and native ownership checks.

This development packet does not prove complete source execution or reference
equality. Finite execution and numerical evidence have separate records.
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
from lark_kernels import collective, native_rope as native
from lark_kernels.ir import lean_list

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modules(name, found):
    if name in found:
        return
    path = ROOT / "lean" / (name.replace(".", "/") + ".lean")
    source = path.read_text()
    found[name] = source
    for line in source.splitlines():
        if line.startswith("import "):
            for imported in line.split()[1:]:
                if imported.startswith("Lark."):
                    modules(imported, found)
                elif imported != "Std":
                    raise ValueError("Unexpected external import " + imported)


def statement(source, contract, *, mutable=(0, 1)):
    tr = native.translate(source, contract)
    task = contract.task
    instructions = ",\n".join(collective.emit(i)[len("(.scalar "):-1] for i in tr.program)
    neox = str(contract.rotary_layout == "split-half").lower()
    return f'''import Lark.NativeRopeAddress
open LarkNonlinear LarkNativeRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def sourceProgram : List Instr := [
{instructions}
]
def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩
def sourceNeox : Bool := {neox}
def sourceGlobal : List Buffer := {lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}
def sourceShared : List Nat := {[v for _, v in tr.shared]}
def sourceMutable : List Nat := {list(mutable)}
def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩
def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩
theorem source_binding : sourceProgram = program sourceNeox ∧
    sourceGlobal = (layout sourceShape).global ∧ sourceShared = (layout sourceShape).shared ∧
    sourceMutable = mutableBuffers ∧ sourceGeometry = geometry sourceShape ∧ sourceFuel = fuel := by decide
theorem source_interface : LarkInOut.Valid (layout sourceShape) mutableBuffers := interface_valid sourceShape
theorem source_pre_satisfiable (input : Nat → Nat → α) :
    ∃ s, LarkInOut.StdPre (layout sourceShape) mutableBuffers input s :=
  LarkInOut.pre_satisfiable _ _ input
theorem source_initial_query (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < sourceShape.rows * 4096) :
    (initial sourceShape input outside).memory ⟨.global, 0, 0, i⟩ = some (input 0 i) :=
  initial_query sourceShape input outside i hi
theorem source_initial_key (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < sourceShape.rows * 1024) :
    (initial sourceShape input outside).memory ⟨.global, 0, 1, i⟩ = some (input 1 i) :=
  initial_key sourceShape input outside i hi
theorem source_initial_cache (input : Nat → Nat → α) (outside : Location → Option α)
    (i : Nat) (hi : i < sourceShape.rows * 128) :
    (initial sourceShape input outside).memory ⟨.global, 0, 2, i⟩ = some (input 2 i) :=
  initial_cache sourceShape input outside i hi
theorem source_pair_coverage (heads col : Nat) (hc : col < heads * 128) :
    ∃ pair < heads * 64, ∃ imaginary : Bool, pairColumn sourceNeox pair imaginary = col :=
  column_coverage sourceNeox heads col hc
theorem source_native_writer (buffer row tid iteration : Nat) (imaginary : Bool)
    (ht : tid < 512) (hi : iteration < (if buffer = 0 then 4 else 1)) :
    writer buffer (address buffer row (tid + iteration * 512) sourceNeox imaginary) sourceNeox = row * 512 + tid :=
  native_writer buffer row tid iteration sourceNeox imaginary ht hi
theorem source_conditional_race_free (trace : List Access)
    (good : ∀ a ∈ trace, Good sourceNeox a) : raceFree (geometry sourceShape) trace = true :=
  race_free sourceShape sourceNeox trace good
#print axioms source_binding
#print axioms source_interface
#print axioms source_pre_satisfiable
#print axioms source_initial_query
#print axioms source_initial_key
#print axioms source_initial_cache
#print axioms source_pair_coverage
#print axioms source_native_writer
#print axioms source_conditional_race_free
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh standalone output must be outside repository")
    out.mkdir(parents=True, exist_ok=False)
    source, own = out / "source", {}
    modules("Lark.NativeRopeAddress", own)
    source_files = []
    for name in own:
        source_files.append("lean/" + name.replace(".", "/") + ".lean")
    source_files += ["lean/lean-toolchain", "lean/lakefile.toml", "LICENSE", "pyproject.toml"]
    source_files += [str(p.relative_to(ROOT)) for p in (ROOT / "lark_kernels").glob("*.py")]
    source_files += [str(p.relative_to(ROOT)) for p in HERE.glob("*.py")]
    for folder in ("cases", "upstream"):
        source_files += [str(p.relative_to(ROOT)) for p in (HERE / folder).rglob("*") if p.is_file()]
    source_files += [str((HERE / "provenance.json").relative_to(ROOT))]
    hashes = {}
    for name in sorted(set(source_files)):
        src, dest = ROOT / name, source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dest)
        hashes[name] = sha(dest)
    (out / "source-manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    with tarfile.open(out / "source.tar.gz", "w:gz") as archive:
        for name in hashes:
            archive.add(source / name, arcname=name, recursive=False)
    checks, audits = [], {}

    def run(name, command, *, accepted=True, audit_count=None):
        start = time.monotonic()
        result = subprocess.run(command, cwd=source / "lean", capture_output=True, text=True, timeout=120)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        if (result.returncode == 0) != accepted:
            raise ValueError("Unexpected Lean result for " + name + ": " + log)
        if accepted:
            found = {m[0]: [v.strip() for v in m[1].split(",") if v.strip()] for m in AUDIT.findall(log)}
            if len(found) != audit_count or any(not set(v) <= ALLOWED for v in found.values()):
                raise ValueError("Axiom audit differs for " + name)
            audits[name] = found
        elif ("false" not in log.lower()
              or re.search(r"maximum recursion|heartbeats|stack overflow|out of memory", log, re.I)):
            raise ValueError("False claim did not fail logically: " + name)
        checks.append({"name": name, "accepted": accepted, "exit_code": result.returncode,
                       "seconds": time.monotonic() - start})

    run("fresh-build", ["lake", "build", "Lark.NativeRopeAddress"], audit_count=27)
    baseline = None
    for kind in native.LAYOUTS:
        for rows in (1, 3, 256, 65535):
            case = HERE / "cases" / kind
            raw = json.loads((case / "task.json").read_text())
            raw["launch"]["grid"] = rows
            for b in raw["buffers"]:
                b["shape"][0] = rows
            contract = native.parse_task(json.dumps(raw))
            native.check_reference((case / "reference.py").read_text(), kind)
            text = (case / "kernel.hip").read_text()
            name = kind.replace("-", "_") + "_" + str(rows)
            (source / "lean" / (name + ".lean")).write_text(statement(text, contract))
            run(name, ["lake", "env", "lean", name + ".lean"], audit_count=9)
            if kind == "interleaved" and rows == 1:
                baseline = text, contract
    text, contract = baseline
    controls = {
        "wrong-query-pair": statement(text.replace("int qx = 2 * qr;", "int qx = 2 * qr + 1;"), contract),
        "wrong-query-stride": statement(text.replace("qi = qi + 512;", "qi = qi + 511;"), contract),
        "wrong-cache-half": statement(text.replace("int qcb = qca + 64;", "int qcb = qca + 63;"), contract),
        "wrong-key-buffer": statement(text.replace("key[ka] =", "query[ka] ="), contract),
        "missing-query-store": statement(text.replace("    query[qb] = __float2half(qoy);\n", ""), contract),
        "wrong-subtraction": statement(text.replace("float qox = qxc - qys;", "float qox = qys - qxc;"), contract),
        "wrong-layout-label": statement((HERE / "cases/split-half/kernel.hip").read_text(), contract),
        "missing-mutable-key": statement(text, contract, mutable=(0,)),
        "denied-pair-inverse": "import Lark.NativeRopeAddress\nopen LarkNativeRope\nexample : pairOfColumn false (pairColumn false 17 true) ≠ 17 := by decide\n",
    }
    for name, contents in controls.items():
        file = "control_" + name.replace("-", "_") + ".lean"
        (source / "lean" / file).write_text(contents)
        run(name, ["lake", "env", "lean", file], accepted=False)
    report = {"schema": 1, "status": "native-rope-full-source-interface-and-ownership-checked",
              "local_lean_modules": len(own), "library_axiom_audits": 27,
              "source_instances": 8, "source_axiom_audits_per_instance": 9,
              "false_lean_claims_rejected": len(controls), "axiom_audits": audits, "checks": checks,
              "source_archive_sha256": sha(out / "source.tar.gz"),
              "source_manifest_sha256": sha(out / "source-manifest.json"),
              "full_source_binding_proved": True, "initialized_mutable_interface_proved": True,
              "address_coverage_and_native_ownership_proved": True,
              "conditional_footprint_race_freedom_proved": True,
              "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
              "source_reference_equality_proved": False, "source_certificates": 0,
              "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "modules": len(own), "audits": 99,
                      "source_instances": 8, "false_claims_rejected": len(controls)}))


if __name__ == "__main__":
    main()
