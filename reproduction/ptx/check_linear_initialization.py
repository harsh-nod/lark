"""Cold-check Linear's full compiled initialization; the kernel is incomplete.

This development study executes no captured code and registers no SDK profile.
It builds all seven owned Lean imports from current source under the existing
limits, binds all 179 parsed instructions, proves the actual 50-step prologue
for every original lane, and checks four exact-source binding refusals.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import secrets
import sys
import time
import traceback

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from lark_kernels import ptx_matrix_certificate as common  # noqa: E402
from reproduction.ptx.linear_frontend import prepare  # noqa: E402

MODULES = (*common.MODULES, "PtxLinear", "PtxLinearInit")
TAGS = ("source_program", "contract_layout", "contract_geometry", "actual_prologue")
LIMITS = dict(common.LIMITS)
INPUTS = {"kernel.ptx": "kernel.ptx", "reference.py": "reference.py", "contract.json": "task.json"}
EXPECTED = {
    "kernel.ptx": "5ae52a2a03b700ffebe4de2d10c69e9fc3f34dea2d99e1bd3ad1c2472ef6e273",
    "reference.py": "e9be42251e3c805b12dab2b8cdf23a8a8d30999c4733ced7a46d7da88c13aa68",
    "contract.json": "78eef07eb3d9a315e87f3bb8bbb6e8a253d6d90a5ada37b1e48351c31dc93dd3",
}
CHANGES = (
    ("wrong-product", "mul.rn.f32", "add.rn.f32"),
    ("wrong-sign-source", "cvt.s64.s32 \t%rd18, %r11;", "cvt.s64.s32 \t%rd18, %r10;"),
    ("wrong-bias-shift", "shl.b64 \t%rd48, %rd18, 1;", "shl.b64 \t%rd48, %rd18, 2;"),
    ("wrong-bias-operation", "add.rn.f32 \t%f68, %f69, %f67;", "mul.rn.f32 \t%f68, %f69, %f67;"),
)


def render(source, reference, contract):
    _, translation = prepare(source, reference, contract)
    return (
        "import Lark.PtxLinearInit\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
        "namespace LarkPtxLinearInitialization\nopen LarkNonlinear LarkPtxPointwise\n"
        "def program : List LarkPtxLinear.Instruction := " + translation.lean_program() + "\n"
        "theorem source_program : program = LarkPtxLinear.Linear.program := by decide\n"
        "theorem contract_layout : LarkPtxLinear.Linear.layout =\n"
        "    ⟨[⟨.input, 64*256⟩, ⟨.input, 256*512⟩, ⟨.input, 512⟩, ⟨.output, 64*512⟩], [], []⟩ := rfl\n"
        "theorem contract_geometry : LarkPtxLinear.Linear.geometry = ⟨32768, 1, 32⟩ := rfl\n"
        "theorem actual_prologue (ops : Ops α) (t : Nat) (base : State α) (ht : t < 32768) :\n"
        "    ∃ final, LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry\n"
        "      t program (LarkPtxLinear.Linear.start base) final ∧\n"
        "      LarkPtxLinear.Linear.Init.Ready ops t base final := by\n"
        "  rw [source_program]\n  exact LarkPtxLinear.Linear.Init.prologue_ready ops t base ht\n"
        + "\n".join("#print axioms LarkPtxLinearInitialization." + tag for tag in TAGS)
        + "\nend LarkPtxLinearInitialization\n"
    )


def run(output, lean_path, owner_token):
    output = common.fresh_output(output)
    lean, version = common.toolchain(lean_path)
    folder = ROOT / "reproduction/ptx/full-size/linear"
    inputs = {name: (folder / path).read_bytes() for name, path in INPUTS.items()}
    common.require({n: common.sha(v) for n, v in inputs.items()} == EXPECTED,
                   "The original compiled inputs must retain their exact bytes")
    task, translation = prepare(*(inputs[n].decode() for n in INPUTS))
    sources = common.own_sources()
    for name in ("PtxLinear", "PtxLinearInit"):
        sources["lean/Lark/" + name + ".lean"] = (ROOT / "lean/Lark" / (name + ".lean")).read_bytes()
    sources["reproduction/ptx/linear_frontend.py"] = (ROOT / "reproduction/ptx/linear_frontend.py").read_bytes()
    sources = dict(sorted(sources.items()))
    output.mkdir(parents=True)
    common.write(output / "owner.json", {"pid": os.getpid(), "token": owner_token})
    (output / "driver.py").write_bytes(Path(__file__).read_bytes())
    for name, content in inputs.items():
        (output / name).write_bytes(content)
    common.write(output / "source-bindings.json", {name: common.sha(v) for name, v in sources.items()})
    for name, content in sources.items():
        target = output / "owned-sources" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    common.write(output / "translation.json", translation.data())
    main = render(*(inputs[n].decode() for n in INPUTS))
    (output / "Main.lean").write_text(main)
    report = {
        "schema": 1, "status": "Linear-initialization-source-build-running",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Development proof of the complete original compiled 50instruction prologue "
            "and guarded sign-extension/64bit shift semantics, under the declared abstract machine. "
            "All179 source instructions are bound, all32768 lanes and original shapes/fuel remain. "
            "Four one-fragment controls test exact-source binding only. The 256term matrix loop, "
            "bias epilogue, return, launch composition, extracted reference, outside-memory and "
            "race proofs remain required. No complete kernel certificate or new independent kernel, "
            "original model result, IEEE/NVIDIA conformance or full-paper reproduction is claimed.",
        "actual_instructions": len(translation.instructions), "proved_initial_instructions": 50,
        "actual_registers": len(translation.registers), "actual_backward_branch": [167, 50],
        "shapes": [list(b.shape) for b in task.buffers], "dtypes": [b.dtype for b in task.buffers],
        "launch": {"grid": task.grid, "block": task.block, "warp": task.warp},
        "unchanged_CUDA_fuel": list(task.fuel), "input_bindings": EXPECTED,
        "main_sha256": common.sha(main.encode()), "source_files": len(sources),
        "source_bindings_sha256": common.sha((output / "source-bindings.json").read_bytes()),
        "Lean_binary_sha256": common.sha(lean.read_bytes()), "Lean_version": version,
        "limits": LIMITS, "old_owned_olean_cache_used": False,
        "source_verified_cached_owned_modules_reused": 0, "fresh_owned_modules_built": 0,
        "module_checks": [], "library_axiom_audits": {}, "negative_source_binding_controls": [],
        "source_bound_kernel_proved": False, "source_bound_development_proofs": 0,
        "new_registered_source_certificates": 0, "model_calls": 0, "gpu_trials": 0,
        "original_paper_fully_reproduced": False,
    }
    common.write(output / "results.json", report)
    modules = output / "modules"
    (modules / "Lark").mkdir(parents=True)
    environment = dict(os.environ, LEAN_PATH=str(modules))
    started = time.monotonic()
    for name in MODULES:
        source = "Lark/" + name + ".lean"
        (modules / source).write_bytes(sources["lean/" + source])
        remaining = LIMITS["source_import_build_seconds"] - (time.monotonic() - started)
        common.require(remaining > 0, "Existing source-import aggregate limit exceeded")
        check, log = common.run_lean(lean, ["-o", "Lark/" + name + ".olean", source], modules,
                                     environment, output / (name + ".log"), min(180, remaining))
        check["module"] = "Lark." + name
        report["module_checks"].append(check)
        common.write(output / "results.json", report)
        if check["exit_code"] != 0 or check["timed_out"]:
            report["status"] = "Linear-initialization-source-import-failed"
            common.write(output / "results.json", report)
            common.manifest(output)
            return report
        tags = (common.library_tags(sources, name) if name in common.MODULES else
                re.findall(r"^#print axioms (\S+)", sources["lean/" + source].decode(), re.M))
        report["library_axiom_audits"].update(common.common.audits(log, tags))
        report["fresh_owned_modules_built"] += 1
        common.write(output / "results.json", report)
    report["import_build_seconds"] = time.monotonic() - started
    check, log = common.run_lean(lean, ["Main.lean"], output, environment, output / "Main.log")
    report["Main_check"] = check
    common.write(output / "results.json", report)
    common.require(check["exit_code"] == 0 and not check["timed_out"], "Actual full prologue proof failed")
    report["Main_axiom_audits"] = common.common.audits(
        log, ["LarkPtxLinearInitialization." + tag for tag in TAGS])
    original = inputs["kernel.ptx"].decode()
    for name, before, after in CHANGES:
        common.require(before in original, "Exactly one intended source fragment must exist")
        altered = original.replace(before, after, 1)
        common.require(altered != original, "Negative source mutation must change input")
        negative = output / name
        negative.mkdir()
        (negative / "kernel.ptx").write_text(altered)
        (negative / "Main.lean").write_text(render(altered, inputs["reference.py"].decode(), inputs["contract.json"].decode()))
        check, log = common.run_lean(lean, ["Main.lean"], negative, environment, negative / "Main.log")
        common.write(negative / "check.json", check)
        common.require(check["exit_code"] != 0 and not check["timed_out"]
                       and "tactic 'decide' proved that" in log and "is false" in log
                       and not any(term in log for term in (
                           "maximum recursion", "maximum number of heartbeats", "Stack overflow")),
                       "Each negative must fail at the actual source equality, without a budget failure")
        report["negative_source_binding_controls"].append({"name": name, **check})
        common.write(output / "results.json", report)
    report["status"] = "cold-source-complete-Linear-initialization-passed-kernel-incomplete"
    report["seconds"] = time.monotonic() - started
    common.write(output / "results.json", report)
    common.manifest(output)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    args = parser.parse_args()
    owner_token = secrets.token_hex(16)
    try:
        result = run(args.output, args.lean, owner_token)
    except Exception as error:
        output = args.output.resolve()
        try:
            owned = common.read(output / "owner.json") == {"pid": os.getpid(), "token": owner_token}
        except (OSError, ValueError):
            owned = False
        if owned:
            (output / "exception.txt").write_text(traceback.format_exc())
            path = output / "results.json"
            failed = common.read(path) if path.exists() else {}
            failed.update(status="Linear-initialization-driver-failed", error_type=type(error).__name__,
                          error=str(error), source_bound_kernel_proved=False,
                          source_bound_development_proofs=0, original_paper_fully_reproduced=False)
            common.write(path, failed)
            common.manifest(output)
        raise
    print(json.dumps({k: result.get(k) for k in (
        "status", "fresh_owned_modules_built", "source_files", "import_build_seconds", "seconds",
        "source_bound_kernel_proved", "original_paper_fully_reproduced")}), flush=True)
    return 0 if result["status"] == "cold-source-complete-Linear-initialization-passed-kernel-incomplete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
