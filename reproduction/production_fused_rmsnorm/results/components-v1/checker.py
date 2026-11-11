"""Fresh standalone check of native in-out identity and proof components.

This does not establish whole-source execution, actual-trace classification,
reference equivalence, IEEE equivalence or original-paper reproduction.
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
from lark_kernels import collective, native_fused_rmsnorm as native
from lark_kernels.ir import lean_list

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modules(name, found):
    if name in found:
        return
    path = ROOT / "lean" / (name.replace(".", "/") + ".lean")
    text = path.read_text()
    found[name] = text
    for line in text.splitlines():
        if line.startswith("import "):
            for imported in line.split()[1:]:
                if imported.startswith("Lark."):
                    modules(imported, found)
                elif imported != "Std":
                    raise ValueError("Unexpected external import " + imported)


def statement(source, contract, *, mutable=(0, 1)):
    tr = native.translate(source, contract)
    task = contract.task
    return """import Lark.NativeFusedRmsNormAddress
open LarkNonlinear LarkNativeFusedRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def sourceProgram : List LarkCollective.Instr := [
""" + ",\n".join(collective.emit(i) for i in tr.program) + f"""
]
def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩
def sourceGlobal : List Buffer := {lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)}
def sourceShared : List Nat := {[n for _, n in tr.shared]}
def sourceMutable : List Nat := {list(mutable)}
def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩
def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩
theorem source_binding : sourceProgram = program ∧
    sourceGlobal = (layout sourceShape).global ∧ sourceShared = (layout sourceShape).shared ∧
    sourceMutable = mutableBuffers ∧ sourceFuel = fuel ∧ sourceGeometry = geometry sourceShape := by decide
theorem source_interface : LarkInOut.Valid (layout sourceShape) mutableBuffers := interface_valid sourceShape
theorem source_pre_satisfiable (input : Nat → Nat → α) :
    ∃ s, LarkInOut.StdPre (layout sourceShape) mutableBuffers input s :=
  LarkInOut.pre_satisfiable _ _ input
#print axioms source_binding
#print axioms source_interface
#print axioms source_pre_satisfiable
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("Fresh standalone output must be outside the repository")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    own = {}
    modules("Lark.NativeFusedRmsNormAddress", own)
    for name, text in own.items():
        dest = project / (name.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
    (project / "lakefile.toml").write_text('''name = "fused_components"
version = "0.1.0"
defaultTargets = ["Main"]
[[lean_lib]]
name = "Lark"
[[lean_lib]]
name = "Main"
''')
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    case = HERE / "cases/native_16384"
    source = (case / "kernel.hip").read_text()
    contract = native.parse_task((case / "task.json").read_text())
    native.check_reference((case / "reference.py").read_text())
    (project / "Main.lean").write_text(statement(source, contract))
    python_sources = project / "lark_kernels"
    python_sources.mkdir()
    for module in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(module, python_sources / module.name)
    source_dir = project / "native-source"
    source_dir.mkdir()
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(case / name, source_dir / name)
    (project / "validate_source.py").write_text('''from pathlib import Path
from lark_kernels import collective, native_fused_rmsnorm as native
from lark_kernels.ir import lean_list

root = Path(__file__).resolve().parent
case = root / "native-source"
contract = native.parse_task((case / "task.json").read_text())
native.check_reference((case / "reference.py").read_text())
translation = native.translate((case / "kernel.hip").read_text(), contract)
main = (root / "Main.lean").read_text()
body = main.split("def sourceProgram : List LarkCollective.Instr := [\\n", 1)[1].split("\\n]\\n", 1)[0]
assert body == ",\\n".join(collective.emit(i) for i in translation.program)
task = contract.task
assert f"def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩" in main
global_text = lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)
assert f"def sourceGlobal : List Buffer := {global_text}" in main
assert f"def sourceShared : List Nat := {[n for _, n in translation.shared]}" in main
assert f"def sourceMutable : List Nat := {list(contract.inout)}" in main
assert f"def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩" in main
assert f"def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩" in main
print("Frozen reader, exact readback, reference and source-to-Main IR/interface replay passed.")
''')
    (project / "README.md").write_text(
        "Source/reader replay: python3 validate_source.py\nFresh build: lake build\n"
        "Controls: lake env lean CONTROL.lean (each must fail)\n"
        "In-out interface, source identity, address coverage and conditional footprints only.\n"
        "No complete source certificate, actual-trace classification or IEEE theorem.\n")
    checks = []

    def execute(name, command, expected):
        start = time.monotonic()
        run = subprocess.run(command, cwd=project, capture_output=True, text=True, timeout=300)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "sorryAx" not in log and "error:" not in log
        if accepted != expected:
            raise ValueError(name + ": unexpected acceptance\n" + log)
        if not expected and ("error:" not in log or "is false" not in log):
            raise ValueError(name + ": rejection did not reach the false-claim gate\n" + log)
        checks.append({"name": name, "expected_accepted": expected, "accepted": accepted,
                       "exit_code": run.returncode, "seconds": time.monotonic() - start,
                       "timed_out": False})
        return log

    execute("frozen-reader-replay", [sys.executable, "validate_source.py"], True)
    log = execute("fresh-build", ["lake", "build"], True)
    audits = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(audits) < 23:
        raise ValueError("Principal axiom audits absent")
    for name, ax in audits:
        if set(x.strip() for x in ax.split(",") if x.strip()) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("Extra axiom in " + name)
    variants = {
        "removed-first-barrier": source.replace("__syncthreads();", "", 1),
        "wrong-shared-owner": source.replace("unrounded[column] = x", "unrounded[component] = x"),
        "unguarded-partial-store": source.replace("if (lane == 0) { partial[warp] = sum; }", "partial[warp] = sum;"),
        "rounded-output-source": source.replace("float value = unrounded[output_column];", "float value = __half2float(residual[output_address]);"),
    }
    for name, variant in variants.items():
        if variant == source:
            raise ValueError("No-op control")
        (project / (name + ".lean")).write_text(statement(variant, contract))
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    name = "missing-residual-inout-binding"
    (project / (name + ".lean")).write_text(statement(source, contract, mutable=(0,)))
    execute(name, ["lake", "env", "lean", name + ".lean"], False)
    base = """import Lark.NativeFusedRmsNormAddress
open LarkNonlinear LarkNativeFusedRmsNorm
def p : Shape := ⟨1, by decide, by decide⟩
def values (b i : Nat) : Nat := b * 7 + i + 1
"""
    claims = {
        "unseeded-input-value": "(LarkNonlinear.initial (layout p) values (fun _ => none)).memory ⟨.global,0,0,0⟩ = some 1",
        "unseeded-residual-value": "(LarkNonlinear.initial (layout p) values (fun _ => none)).memory ⟨.global,0,1,0⟩ = some 8",
        "write-readonly-weight": "location (layout p) (geometry p) 0 .global 2 0 true = some ⟨.global,0,2,0⟩",
        "seed-foreign-owner": "(initial p values (fun _ => none)).memory ⟨.global,1,0,0⟩ = some 1",
    }
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
    report = {"schema": 1, "status": "native-inout-components-checked", "local_lean_modules": len(own),
              "axiom_audits": dict(audits), "false_claims_rejected": sum(not c["expected_accepted"] for c in checks),
              "frozen_python_reader_replayed": True,
              "fresh_standalone_build": True, "source_archive_sha256": sha(out / "source.tar.gz"),
              "source_kernel_sha256": sha(case / "kernel.hip"), "checks": checks,
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_trace_classification_proved": False, "canonical_source_equivalence_proved": False,
              "gpu_trials": 0, "model_calls": 0, "original_paper_fully_reproduced": False,
              "scope": "In-out initialization/non-vacuity, exact source/layout/interface binding, address coverage/unique ownership and sufficient footprint lemmas. Actual source trace classification and whole-launch/reference proofs remain open."}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest = {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "local_lean_modules", "false_claims_rejected", "source_certificates")}), flush=True)


if __name__ == "__main__":
    main()
