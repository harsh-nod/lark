"""Cold-check the independent full-size FFN reference, not a kernel certificate."""

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
    for name in ["Nonlinear", "Pointwise", "PtxPointwise", "PtxDot", "PtxMatrix", "PtxFeedForwardUp"]:
        shutil.copy2(ROOT / "lean/Lark" / (name + ".lean"), source / "Lark" / (name + ".lean"))
    shutil.copytree(
        ROOT / "lark_kernels", OUT / "tool-sources", ignore=shutil.ignore_patterns("__pycache__")
    )
    (source / "Main.lean").write_text("""import Lark.PtxFeedForwardUp
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkCompiledFfnUpInput
open LarkNonlinear LarkPtxDot LarkPtxMatrix LarkPtxFeedForwardUp
 def parsed : List Instruction := """ + parsed[0].lean_program() + """
theorem exact_source : parsed = Up.program := by decide
theorem source_to_loop (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 65536) (hreads : Up.Reads input (Up.start s)) :
    Steps ops Up.layout Up.geometry t parsed (Up.start s) (Up.loopExit ops input t s) ∧
    Up.LoopInvariant input t 16 (Up.dotValue ops input t) (Up.loopExit ops input t s) := by
  rw [exact_source]
  exact Up.source_to_loop_exit ops input t s ht hreads
#print axioms exact_source
#print axioms source_to_loop
end LarkCompiledFfnUpInput
""")
    write(
        "prepared-inputs.json",
        {
            "instructions": [len(t.instructions) for t in parsed],
            "grid": [t.grid for t in tasks],
            "fuel": [list(t.fuel) for t in tasks],
            "reference_body": body,
            "scope": "Full original up-stage prologue and all256 dot terms only; output epilogue and pipeline still unproved.",
        },
    )
    env = dict(os.environ, LEAN_PATH=str(source), PYTHONNOUSERSITE="1")
    env.pop("PYTHONPATH", None)
    started = time.monotonic()
    checks = []
    audits = {}
    code = 0
    for name in ["Nonlinear", "Pointwise", "PtxPointwise", "PtxDot", "PtxMatrix", "PtxFeedForwardUp", "Main"]:
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
        prefix = {"Nonlinear":"LarkNonlinear", "Pointwise":"LarkPointwise", "PtxPointwise":"LarkPtxPointwise", "PtxDot":"LarkPtxDot", "PtxMatrix":"LarkPtxMatrix", "PtxFeedForwardUp":"LarkPtxFeedForwardUp", "Main":"LarkCompiledFfnUpInput"}[name]
        tags = [n if n.startswith(prefix + ".") else prefix + "." + n for n in re.findall(r"^#print axioms (\S+)", (source / relative).read_text(), re.M)]
        audits.update(common.audits((OUT / (name + ".log")).read_text(), tags))
    result = {
        "status": "exact-full-size-FFN-up-prologue-and-loop-passed"
        if code == 0 and len(checks) == 7
        else "failed-up-stage-development-check",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "module_checks": checks,
        "axiom_audits": audits,
        "total_seconds": time.monotonic() - started,
        "Lean_sha256": sha(LEAN),
        "original_stack_limits": resource.getrlimit(resource.RLIMIT_STACK),
        "limits": common.LIMITS,
        "all_own_modules_fresh": True,
        "source_import_build_seconds": 600,
        "compiled_FFN_kernel_correctness_proofs": 0,
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
    print(json.dumps(result), flush=True)
    raise SystemExit(0 if result["status"].endswith("-passed") else 1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    args = parser.parse_args()
    main(args.output, args.lean)
