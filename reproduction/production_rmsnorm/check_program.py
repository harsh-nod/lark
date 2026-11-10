"""Bind actual frontend IR to the fixed Lean program, with direct negative controls.

This checks program identity, not execution or whole-kernel correctness.
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
from lark_kernels import collective, native_rmsnorm, partition_collective  # noqa: E402

HERE = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    case = HERE / "cases/weighted_16384"
    task = native_rmsnorm.parse_task((case / "task.json").read_text())
    source = (case / "kernel.hip").read_text()
    built = subprocess.run(
        ["lake", "build", "Lark.NativeRmsNormValue"],
        cwd=ROOT / "lean",
        capture_output=True,
        text=True,
        timeout=300,
    )
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode or "sorryAx" in built.stdout + built.stderr:
        raise RuntimeError("Proof library did not build")
    results = []
    changes = {
        "baseline": source,
        "wrong-final-offset": source.replace(
            "__shfl_down(variance, 8, 16)", "__shfl_down(variance, 4, 16)"
        ),
        "removed-first-barrier": source.replace("  __syncthreads();", "", 1),
        "wrong-weight-index": source.replace("weight[outVector * 8 + outComponent]", "weight[0]"),
        "unguarded-partial-store": source.replace(
            "if (lane == 0) { partials[warp] = variance; }", "partials[warp] = variance;"
        ),
    }
    for name, changed in changes.items():
        dest = out / name
        dest.mkdir()
        (dest / "kernel.hip").write_text(changed)
        tr = partition_collective.translate(changed, task)
        code = (
            """import Lark.NativeRmsNormValue
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
def sourceProgram : List LarkCollective.Instr := [
"""
            + ",\n".join(collective.emit(i) for i in tr.program)
            + """]
theorem source_binding : sourceProgram = LarkNativeRmsNorm.program := by decide
#print axioms source_binding
"""
        )
        (dest / "Main.lean").write_text(code)
        start = time.monotonic()
        checked = subprocess.run(
            ["lake", "env", "lean", str(dest / "Main.lean")],
            cwd=ROOT / "lean",
            capture_output=True,
            text=True,
            timeout=120,
        )
        log = checked.stdout + checked.stderr
        (dest / "lean.log").write_text(log)
        accepted = checked.returncode == 0 and "sorryAx" not in log and "error:" not in log
        if accepted != (name == "baseline") or (
            not accepted and ("error:" not in log or "maximum" in log or "Stack overflow" in log)
        ):
            raise RuntimeError("Unexpected direct program-binding result: " + name + "\n" + log)
        results.append(
            {
                "name": name,
                "accepted": accepted,
                "instructions": len(tr.program),
                "wall_seconds": time.monotonic() - start,
            }
        )
    report = {
        "status": "passed",
        "claim": "source IR identity only",
        "complete_source_proof": False,
        "certificates": 0,
        "direct_lean_binding_rejections": 4,
        "cases": results,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    files = {
        str(p.relative_to(out)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.rglob("*"))
        if p.is_file()
    }
    (out / "manifest.json").write_text(json.dumps(files, indent=2) + "\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
