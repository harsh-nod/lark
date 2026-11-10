"""Rebuild the native attention lane prefix outside Git, without model/GPU calls.

This checks source identity and actual runLane execution through the first block
barrier. It is not a whole-launch or source-reference certificate.
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
TARGET = "Lark.NativeAttentionFirstLane"
AUDITS = ("first_lane_eq", "first_lane_run", "first_lane_output", "first_lane_tile", "first_lane_reads",
          "first_lane_good", "first_lane_race_free")


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
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    standalone = out / "source"
    standalone.mkdir()
    task = native.parse_task((CASE / "task.json").read_text())
    source = (CASE / "kernel.hip").read_bytes().decode()
    native.check_reference((CASE / "reference.py").read_text(), task)
    provenance = json.loads((HERE / "native-provenance.json").read_text())
    require(sha(CASE / "kernel.hip") == provenance["native_source_sha256"], "Native source changed")
    translated = native.translate(source, task)
    modules = sorted(closure(TARGET))
    for module in modules:
        name = module.replace(".", "/") + ".lean"
        dest = standalone / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean" / name, dest)
    shutil.copyfile(ROOT / "lean/lean-toolchain", standalone / "lean-toolchain")
    (standalone / "lakefile.toml").write_text(
        'name = "native_attention_prefix"\nversion = "0.1.0"\n'
        'defaultTargets = ["Lark.NativeAttentionFirstLane"]\n\n[[lean_lib]]\nname = "Lark"\n')
    header = f"import {TARGET}\nopen LarkNonlinear LarkNativeAttention\n"
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
""" + "\n".join("#print axioms " + n for n in AUDITS) + "\n"
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
    (standalone / "README.md").write_text(
        "# Native attention lane-prefix proof\n\n"
        "Run `lake build`, then `lake env lean Main.lean` with Lean 4.19.0.\n"
        "The three other top-level Lean files intentionally fail at false postconditions.\n"
        "This proves each lane reaches PC 20. It does not compose the launch, resume\n"
        "the barrier, execute attention computation, or prove dense-reference equality.\n")
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
    for name in AUDITS:
        entries = re.findall(r"^'LarkNativeAttention\." + name +
                             r"' depends on axioms: \[([^]]*)\]$", log, re.M)
        require(len(entries) == 1, "Missing or ambiguous axiom audit: " + name)
        axioms = entries[0].split(", ") if entries[0] else []
        require(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
        audits[name] = axioms
    report = {
        "schema": 1, "status": "native-lane-prefix-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "actual runLane from PC 0 through 5405 instructions to first block barrier PC 20",
        "groups": {"min": 1, "max": 65535}, "block": 32, "warp": 64,
        "prefix_instructions_per_lane": 5405, "barrier_pc": 20,
        "input_preservation_proved": True, "output_initialization_proved": True,
        "first_kv_row_copy_proved": True, "prefix_actual_trace_race_freedom_proved": True,
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
