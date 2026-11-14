"""Cold-check the full-size compiled FFN up stage; the composed FFN remains unproved."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path('/tmp/lark-ptx-ffn-refinement-20261114')
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_ffn, ptx_pointwise_certificate as common  # noqa: E402


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main(output, lean):
    OUT, LEAN = output.resolve(), lean.resolve()

    def write(name, value):
        (OUT / name).write_text(json.dumps(value, indent=2) + "\n")

    OUT.mkdir(exist_ok=False)
    (OUT / "driver.py").write_bytes(Path(__file__).read_bytes())
    assert sha(LEAN) == common.LEAN_SHA256
    source = OUT / "source"
    (source / "Lark").mkdir(parents=True)
    inputs = ROOT / "reproduction/ptx/full-size/ffn"
    shutil.copytree(inputs, OUT / "inputs")
    tasks, parsed, body = ptx_ffn.prepare(
        *[(inputs / s / "kernel.ptx").read_text() for s in ("up", "down")],
        (inputs / "reference.py").read_text(),
        *[(inputs / s / "task.json").read_text() for s in ("up", "down")],
    )
    for name in [
        "Nonlinear",
        "Pointwise",
        "PtxPointwise",
        "PtxDot",
        "PtxMatrix",
        "PtxFeedForwardUp",
        "PtxFeedForwardDownInit",
        "PtxFeedForwardDown",
        "PtxFeedForwardReference",
        "PtxFeedForwardDownExit",
        "PtxFeedForwardDownLaunch",
    ]:
        shutil.copy2(ROOT / "lean/Lark" / (name + ".lean"), source / "Lark" / (name + ".lean"))
    shutil.copytree(
        ROOT / "lark_kernels", OUT / "tool-sources", ignore=shutil.ignore_patterns("__pycache__")
    )
    (source / "Main.lean").write_text("""import Lark.PtxFeedForwardDownLaunch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkCompiledFfnDownInput
open LarkNonlinear LarkPtxDot LarkPtxMatrix
 def parsed : List LarkPtxMatrix.Instruction := """ + parsed[1].lean_program() + """
theorem exact_source : parsed = FfnDown.program := by decide
theorem whole_prologue (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    LarkPtxMatrix.Steps ops FfnDown.layout FfnDown.geometry t parsed
      (FfnDown.start s) (FfnDown.initialized ops t s) := by
  rw [exact_source]
  exact FfnDown.prologue_execute ops t s ht
theorem whole_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 16384) (hreads : FfnDown.Reads input (FfnDown.start s)) :
    LarkPtxMatrix.Steps ops FfnDown.layout FfnDown.geometry t parsed
      (FfnDown.start s) (FfnDown.loopExit ops input t s) ∧
    FfnDown.LoopInvariant input t 64 (FfnDown.dotValue ops input t) (FfnDown.loopExit ops input t s) := by
  rw [exact_source]
  exact FfnDown.source_to_loop_exit ops input t s ht hreads
#print axioms whole_loop
theorem full_down_stage_correct (ops : Ops α) :
    FfnDown.Correct ops parsed (FfnDown.referenceSpec ops) := by
  rw [exact_source]
  exact FfnDown.kernel_correct ops
#print axioms full_down_stage_correct
#print axioms exact_source
#print axioms whole_prologue
end LarkCompiledFfnDownInput
""")
    write(
        "prepared-inputs.json",
        {
            "instructions": [len(t.instructions) for t in parsed],
            "grid": [t.grid for t in tasks],
            "fuel": [list(t.fuel) for t in tasks],
            "reference_body": body,
            "scope": "Exact full down-stage launch, independent reference, all16384 outputs, actual race freedom and frame property; pipeline still unproved.",
        },
    )
    env = dict(os.environ, LEAN_PATH=str(source), PYTHONNOUSERSITE="1")
    env.pop("PYTHONPATH", None)
    started = time.monotonic()
    checks = []
    audits = {}
    code = 0
    for name in [
        "Nonlinear",
        "Pointwise",
        "PtxPointwise",
        "PtxDot",
        "PtxMatrix",
        "PtxFeedForwardUp",
        "PtxFeedForwardDownInit",
        "PtxFeedForwardDown",
        "PtxFeedForwardReference",
        "PtxFeedForwardDownExit",
        "PtxFeedForwardDownLaunch",
        "Main",
    ]:
        relative = "Main.lean" if name == "Main" else "Lark/" + name + ".lean"
        command = [str(LEAN), "-o", relative.removesuffix(".lean") + ".olean", relative]
        limit = min(180, 600 - (time.monotonic() - started))
        assert limit > 0
        begin = time.monotonic()
        timed_out = False
        with (OUT / (name + ".log")).open("wb") as output:
            child = subprocess.Popen(
                command,
                cwd=source,
                env=env,
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            write(
                "progress.json",
                {"pid": os.getpid(), "child_pid": child.pid, "stage": name, "command": command},
            )
            try:
                code = child.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
        checks.append(
            {
                "module": name,
                "command": command,
                "exit_code": code,
                "timed_out": timed_out,
                "seconds": time.monotonic() - begin,
            }
        )
        if code or timed_out:
            break
        prefix = {
            "Nonlinear": "LarkNonlinear",
            "Pointwise": "LarkPointwise",
            "PtxPointwise": "LarkPtxPointwise",
            "PtxDot": "LarkPtxDot",
            "PtxMatrix": "LarkPtxMatrix",
            "PtxFeedForwardUp": "LarkPtxMatrix",
            "PtxFeedForwardUpExit": "LarkPtxMatrix",
            "PtxFeedForwardUpLaunch": "LarkPtxMatrix",
            "PtxFeedForwardDownInit": "LarkPtxMatrix",
            "PtxFeedForwardDown": "LarkPtxMatrix",
            "PtxFeedForwardDownExit": "LarkPtxMatrix",
            "PtxFeedForwardDownLaunch": "LarkPtxMatrix",
            "PtxFeedForwardReference": "LarkPtxFeedForward.Reference",
            "Main": "LarkCompiledFfnDownInput",
        }[name]
        tags = [
            n if n.startswith(prefix + ".") else prefix + "." + n
            for n in re.findall(r"^#print axioms (\S+)", (source / relative).read_text(), re.M)
        ]
        audits.update(common.audits((OUT / (name + ".log")).read_text(), tags))
    result = {
        "status": "exact-full-size-FFN-down-launch-reference-race-frame-passed"
        if code == 0 and len(checks) == 12
        else "failed-down-stage-development-check",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "module_checks": checks,
        "axiom_audits": audits,
        "total_seconds": time.monotonic() - started,
        "Lean_sha256": sha(LEAN),
        "original_stack_limits": resource.getrlimit(resource.RLIMIT_STACK),
        "limits": common.LIMITS,
        "all_own_modules_fresh": True,
        "source_import_build_seconds": 600,
        "compiled_FFN_up_stage_correctness_proofs": 0,
        "compiled_FFN_down_stage_correctness_proofs": int(code == 0 and len(checks) == 12),
        "compiled_FFN_pipeline_correctness_proofs": 0,
        "new_registered_source_certificates": 0,
        "GPU_trials": 0,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
    }
    write("results.json", result)
    write(
        "manifest.json",
        {p.relative_to(OUT).as_posix(): sha(p) for p in sorted(OUT.rglob("*")) if p.is_file()},
    )
    print(json.dumps({"status":result["status"],"total_seconds":result["total_seconds"],"axiom_audits":len(audits)}), flush=True)
    raise SystemExit(0 if result["status"].endswith("-passed") else 1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    args = parser.parse_args()
    main(args.output, args.lean)
