"""Fresh source-bound per-lane scalar-prefix proof; no GPU/model calls.

This proves the actual 210-instruction prefix through both in-place rounds,
ending at PC23 before any shuffle. Whole-launch and canonical-real source
correctness remain open. Existing frozen component/GPU packets are unchanged.
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
from lark_kernels import native_fused_rmsnorm as native  # noqa: E402
from reproduction.production_fused_rmsnorm import check_program as component  # noqa: E402

HERE = Path(__file__).resolve().parent
CASE = HERE / "cases/native_16384"
TARGET = "Lark.NativeFusedRmsNormPrefix"
SOURCE_SHA256 = "c297c1842c1a4d2d9be2265aa0d03da759dda22f555947e3483eccb486e5f59e"
PRINCIPAL = (
    "source_binding", "source_prefix_all_shapes", "source_prefix_values",
    "source_prefix_good", "source_prefix_race_free", "source_prefix_access_count",
    "LarkNativeFusedRmsNorm.component_cycle", "LarkNativeFusedRmsNorm.components_eq",
    "LarkNativeFusedRmsNorm.round_eq", "LarkNativeFusedRmsNorm.prefix_eq",
    "LarkNativeFusedRmsNorm.initial_prefix_run", "LarkNativeFusedRmsNorm.initial_prefix_values",
    "LarkNativeFusedRmsNorm.initial_prefix_good", "LarkNativeFusedRmsNorm.initial_prefix_race_free",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def statement(source, contract):
    identity = component.statement(source, contract).replace(
        "import Lark.NativeFusedRmsNormAddress", f"import {TARGET}", 1)
    return identity + """
theorem source_prefix_all_shapes (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) sourceProgram t sourceFuel.lane
      (initial p input outside) = some (prefixState ops input t (initial p input outside)) := by
  simpa only [source_binding.1, source_binding.2.2.2.2.1] using initial_prefix_run p ops input outside t ht
theorem source_prefix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    (prefixState ops input t (initial p input outside)).regs t 0 =
      some (threadSum ops input (t / 1024) (t % 1024)) ∧
    Pending input (t / 1024) (t % 1024) 16 (prefixState ops input t (initial p input outside)) ∧
    Completed ops input (t / 1024) (t % 1024) t 16 (prefixState ops input t (initial p input outside)) :=
  initial_prefix_values p ops input outside t ht
theorem source_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    ∀ a ∈ (prefixState ops input t (initial p input outside)).trace, Good a :=
  initial_prefix_good p ops input outside t ht
theorem source_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    raceFree (geometry p) (prefixState ops input t (initial p input outside)).trace = true :=
  initial_prefix_race_free p ops input outside t ht
theorem source_prefix_access_count (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (prefixState ops input t (initial p input outside)).trace.length = 64 :=
  initial_prefix_trace_length p ops input outside t
#print axioms source_prefix_all_shapes
#print axioms source_prefix_values
#print axioms source_prefix_good
#print axioms source_prefix_race_free
#print axioms source_prefix_access_count
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Fresh standalone output must be outside a Git checkout")
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    own = {}
    component.modules(TARGET, own)
    for name, text in own.items():
        dest = project / (name.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
    (project / "lakefile.toml").write_text('''name = "fused_scalar_prefix"
version = "0.1.0"
defaultTargets = ["Main"]
[[lean_lib]]
name = "Lark"
[[lean_lib]]
name = "Main"
''')
    shutil.copyfile(ROOT / "LICENSE", project / "LICENSE")
    source = (CASE / "kernel.hip").read_text()
    if sha(CASE / "kernel.hip") != SOURCE_SHA256:
        raise ValueError("Pinned source changed")
    contract = native.parse_task((CASE / "task.json").read_text())
    native.check_reference((CASE / "reference.py").read_text())
    (project / "Main.lean").write_text(statement(source, contract))
    reader_dir = project / "lark_kernels"
    reader_dir.mkdir()
    for path in sorted((ROOT / "lark_kernels").glob("*.py")):
        shutil.copyfile(path, reader_dir / path.name)
    source_dir = project / "native-source"
    source_dir.mkdir()
    for name in ("kernel.hip", "reference.py", "task.json"):
        shutil.copyfile(CASE / name, source_dir / name)
    shutil.copyfile(HERE / "provenance.json", source_dir / "provenance.json")
    licenses = project / "licenses"
    licenses.mkdir()
    for name in ("FLASHINFER_LICENSE", "SGLANG_LICENSE"):
        shutil.copyfile(HERE / "upstream" / name, licenses / name)
    (project / "README.md").write_text(
        "Per-lane native fused add RMSNorm scalar-prefix proof, ending at PC23.\n"
        "Requires Python 3 and Lean 4.19.0; no Git, GPUs or models.\n"
        "Replay the frozen reader: python3 validate_source.py\n"
        "Rebuild from source: lake build\n"
        "Positive concrete witnesses: lake env lean Witnesses.lean\n"
        "Every other top-level .lean file except Main.lean is a control that must\n"
        "fail with 'is false' at its assertion. No .lake objects are archived.\n"
        "All inputs/operations/outside memory and valid lanes/rows1..255 are\n"
        "quantified by the prefix theorem. This is not a full kernel certificate.\n"
        "Logical32 shuffles, barriers, output normalization, halt, scheduling,\n"
        "canonical-real/IEEE equivalence and original-paper results remain open.\n")
    # The archived replay derives the translated IR again from frozen source,
    # without importing the live checkout or depending on Git.
    (project / "validate_source.py").write_text('''from pathlib import Path
import hashlib
from lark_kernels import collective, native_fused_rmsnorm as native
from lark_kernels.ir import lean_list
root = Path(__file__).resolve().parent
case = root / "native-source"
assert hashlib.sha256((case / "kernel.hip").read_bytes()).hexdigest() == "c297c1842c1a4d2d9be2265aa0d03da759dda22f555947e3483eccb486e5f59e"
contract = native.parse_task((case / "task.json").read_text())
native.check_reference((case / "reference.py").read_text())
translation = native.translate((case / "kernel.hip").read_text(), contract)
main = (root / "Main.lean").read_text()
body = main.split("def sourceProgram : List LarkCollective.Instr := [\\n", 1)[1].split("\\n]\\n", 1)[0]
assert body == ",\\n".join(collective.emit(i) for i in translation.program)
task = contract.task
assert f"def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩" in main
globals_text = lean_list(f"⟨.{b.role}, {b.size}⟩" for b in task.buffers)
assert f"def sourceGlobal : List Buffer := {globals_text}" in main
assert f"def sourceShared : List Nat := {[n for _, n in translation.shared]}" in main
assert f"def sourceMutable : List Nat := {list(contract.inout)}" in main
assert f"def sourceFuel : Fuel := ⟨{','.join(map(str, task.fuel))}⟩" in main
assert f"def sourceGeometry : Geometry := ⟨{task.grid},{task.block},{task.warp}⟩" in main
print("Frozen source/reader/IR/interface/fuel binding replay passed.")
''')
    checks = []

    def execute(name, command, expected=True):
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
                       "exit_code": run.returncode, "seconds": time.monotonic() - start, "timed_out": False})
        return log

    execute("frozen-reader-replay", [sys.executable, "validate_source.py"])
    log = execute("fresh-build", ["lake", "build"])
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
    if set(PRINCIPAL) - audits.keys():
        raise ValueError("Principal axiom audits absent: " + str(set(PRINCIPAL) - audits.keys()))
    for name, ax in audits.items():
        if set(x.strip() for x in ax.split(",") if x.strip()) - {"propext", "Classical.choice", "Quot.sound"}:
            raise ValueError("Extra axiom in " + name)
    variants = {
        "skipped-second-round": source.replace("while (iteration < 2)", "while (iteration < 1)", 1),
        "wrong-residual-value": source.replace("__float2half(x);", "__float2half(r);", 1),
        "rounded-shared-value": source.replace("unrounded[column] = x;", "unrounded[column] = __half2float(residual[address]);", 1),
        "wrong-component-stride": source.replace("component = component + 1;", "component = component + 2;", 1),
    }
    for name, variant in variants.items():
        if variant == source:
            raise ValueError("No-op source control")
        (project / (name + ".lean")).write_text(statement(variant, contract))
        execute(name, ["lake", "env", "lean", name + ".lean"], False)
    base = f"""import {TARGET}
open LarkNonlinear LarkNativeFusedRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def p : Shape := ⟨1, by decide, by decide⟩
def ops : Ops Nat := ⟨fun n d => n.toNat / d, (· + ·), (· - ·), (· * ·), Nat.max,
  (· / ·), id, id, id, id, fun x => x + 1000⟩
def values (b i : Nat) : Nat := b * 7 + i + 1
def start : State Nat := initial p values (fun _ => none)
def once : State Nat := componentAfter ops values 0 0 0 0 0 0 start
"""
    claims = {
        "omitted-residual-cast": "once.memory (globalCell 1 0) = some (added ops values 0 0 0 0)",
        "rounded-shared-state": "once.memory (unroundedCell 0 0) = some (ops.toHalf (added ops values 0 0 0 0))",
        "overwritten-unread-residual": "once.memory (globalCell 1 1) = some (ops.toHalf (flatAdded ops values 0 0 1))",
        "rounded-square-accumulation": "once.regs 0 0 = some (ops.mul (ops.toHalf (added ops values 0 0 0 0)) (ops.toHalf (added ops values 0 0 0 0)))",
        "wrong-prefix-endpoint": "(prefixState ops values 0 start).pc 0 = 35",
        "wrong-round-exit": "(endRound 0 0 start).indices 0 4 = some 2",
    }
    # Include positive witnesses so the nonidentity cast controls cannot reject
    # solely because of an invalid concrete setup.
    witnesses = """example : once.memory (globalCell 1 0) = some 1009 := by decide
example : once.memory (unroundedCell 0 0) = some 9 := by decide
example : once.memory (globalCell 1 1) = some 9 := by decide
example : once.regs 0 0 = some 81 := by decide
example : (prefixState ops values 0 start).pc 0 = 23 := by decide
"""
    (project / "Witnesses.lean").write_text(base + witnesses)
    execute("positive-cast-and-preservation-witnesses", ["lake", "env", "lean", "Witnesses.lean"])
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
    shutil.copyfile(HERE / "check_program.py", out / "component_checker.py")
    report = {
        "schema": 1, "status": "native-inout-scalar-prefix-checked", "local_lean_modules": len(own),
        "axiom_audits": audits, "false_claims_rejected": sum(not c["expected_accepted"] for c in checks),
        "checks": checks, "fresh_standalone_build": True, "frozen_python_reader_replayed": True,
        "source_archive_sha256": sha(out / "source.tar.gz"), "source_kernel_sha256": sha(CASE / "kernel.hip"),
        "scalar_prefix_execution_proved": True, "scalar_prefix_actual_trace_classification_proved": True,
        "scalar_prefix_race_freedom_proved": True, "scalar_prefix_instruction_count": 210,
        "scalar_prefix_access_count_per_lane": 64, "scalar_prefix_end_pc": 23,
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "canonical_source_equivalence_proved": False,
        "gpu_trials": 0, "model_calls": 0, "original_paper_fully_reproduced": False,
        "scope": "All rows1..255, valid lanes, arbitrary Ops/input/outside; actual seeded initialization and both rounds through first shuffle, all 16 rounded residual and unrounded shared stores, input preservation, source-order local square sum, actual-prefix trace classification/race freedom. Logical32 collectives, both barriers, normalized outputs, halt, scheduler/grid, canonical-real and IEEE equivalence remain open.",
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest = {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "local_lean_modules", "false_claims_rejected", "source_certificates")}), flush=True)


if __name__ == "__main__":
    main()
