"""Bind the full development source IR and check footprint facts in Lean.

Identity checks and sufficient footprint lemmas are not whole-source execution
or race-freedom certificates. No original-paper mutant result is claimed.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_attention as native  # noqa: E402
from lark_kernels.ir import lean_node  # noqa: E402

CASE = Path(__file__).resolve().parent / "cases/native_fp16"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    task = native.parse_task((CASE / "task.json").read_text())
    source = (CASE / "kernel.hip").read_bytes().decode()
    native.check_reference((CASE / "reference.py").read_text(), task)
    built = subprocess.run(["lake", "build", "Lark.NativeAttentionAddress"],
                           cwd=ROOT / "lean", capture_output=True, text=True, timeout=300)
    log = built.stdout + built.stderr
    (out / "build.log").write_text(log)
    if built.returncode or "sorryAx" in log or "error:" in log:
        raise ValueError("Native attention components failed to build")
    candidates = {
        "baseline": source,
        "removed-load-barrier": source.replace("    __syncthreads();", "", 1),
        "wrong-tile-store-owner": source.replace("kj[lane * 256 + load_x]", "kj[load_x]"),
        "wrong-running-state": source.replace("running_m[tile_i]", "running_m[0]"),
        "omitted-old-mass": source.replace("old_l * old_scale * old_o", "1.0f * old_scale * old_o"),
        "shrunken-private-array": source.replace("float running_m[4]", "float running_m[1]"),
    }
    records = []
    for name, candidate in candidates.items():
        if name != "baseline" and candidate == source:
            raise ValueError("Source control did not change anything")
        dest = out / name
        dest.mkdir()
        (dest / "kernel.hip").write_bytes(candidate.encode())
        tr = native.translate(candidate, task)
        code = """import Lark.NativeAttentionAddress
open LarkNonlinear LarkNativeAttention
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
def sourceProgram : List Instr := [
""" + ",\n".join(lean_node(i) for i in tr.program) + f"""
]
def sourceShared : List Nat := {[size for _, size in tr.shared]}
def sourceLocals : List Nat := {[size for _, size in tr.locals]}
def sourceShape : Shape := ⟨{task.grid}, by decide, by decide⟩
theorem source_binding : sourceProgram = program ∧
    sourceShared = (layout sourceShape).shared ∧
    sourceLocals = (layout sourceShape).locals := by decide
#print axioms source_binding
"""
        (dest / "Main.lean").write_text(code)
        started = time.monotonic()
        checked = subprocess.run(["lake", "env", "lean", str(dest / "Main.lean")],
                                 cwd=ROOT / "lean", capture_output=True, text=True, timeout=120)
        log = checked.stdout + checked.stderr
        (dest / "lean.log").write_text(log)
        accepted = checked.returncode == 0 and "sorryAx" not in log and "error:" not in log
        if accepted != (name == "baseline") or (not accepted and ("is false" not in log or "error:" not in log)):
            raise ValueError("Unexpected program identity result: " + name + "\n" + log)
        records.append({"name": name, "accepted": accepted, "instructions": len(tr.program),
                        "seconds": time.monotonic() - started, "timed_out": False})
    witness = out / "footprint-witness.lean"
    witness.write_text('''import Lark.NativeAttentionAddress
open LarkNonlinear LarkNativeAttention
def p : Shape := ⟨1, by decide, by decide⟩
def readAt (epoch : Nat) : Access := ⟨0, ⟨.shared,0,1,256⟩, false, ⟨0,epoch,0⟩⟩
def storeAt : Access := ⟨1, ⟨.shared,0,1,256⟩, true, ⟨0,0,0⟩⟩
example : conflict (geometry p) (readAt 0) storeAt = true := by decide
example : conflict (geometry p) (readAt 1) storeAt = false := by decide
example : Good (readAt 1) := by apply Good.tileLoad <;> decide
example : Good storeAt := by apply Good.tileStore <;> decide
example : raceFree (geometry p) [readAt 1, storeAt] = true := by decide
example : location (layout p) (geometry p) 17 .local 0 0 true = some ⟨.local,17,0,0⟩ := by decide
''')
    checked = subprocess.run(["lake", "env", "lean", str(witness)], cwd=ROOT / "lean",
                             capture_output=True, text=True, timeout=120)
    log = checked.stdout + checked.stderr
    (out / "footprint-witness.log").write_text(log)
    if checked.returncode or "error:" in log or "sorryAx" in log:
        raise ValueError("Native footprint witnesses failed: " + log)
    report = {"status": "passed", "scope": "fixed IR/layout identity and conditional footprint lemmas only",
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_trace_classification_proved": False,
              "direct_lean_identity_rejections": 5, "footprint_witnesses_checked": True,
              "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
              "cases": records}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    hashes = {str(p.relative_to(out)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
