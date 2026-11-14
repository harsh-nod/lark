"""Export and freshly replay the full compiled two-launch FFN development proof.

Replay runs the installed trusted checker. Captured Python, Lean and oleans are
inventory-bound data; none is executed or loaded as a trusted import.
"""

import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import re
import resource
import time

from . import pointwise, ptx_ffn
from . import ptx_pointwise_certificate as common
from .ir import Refusal

INPUTS = ("up/kernel.ptx", "down/kernel.ptx", "reference.py",
          "up/contract.json", "down/contract.json")
LIMITS = dict(common.LIMITS)
LEAN_SHA256 = common.LEAN_SHA256
MODULES = (
    "Nonlinear", "Pointwise", "PtxPointwise", "PtxDot", "PtxMatrix",
    "PtxFeedForwardReference", "PtxFeedForwardUp", "PtxFeedForwardUpExit",
    "PtxFeedForwardUpLaunch", "PtxFeedForwardDownInit", "PtxFeedForwardDown",
    "PtxFeedForwardDownExit", "PtxFeedForwardDownLaunch", "PtxFeedForwardPipeline",
)
NAMESPACES = {
    "Nonlinear": "LarkNonlinear", "Pointwise": "LarkPointwise",
    "PtxPointwise": "LarkPtxPointwise", "PtxDot": "LarkPtxDot",
    "PtxMatrix": "LarkPtxMatrix",
    "PtxFeedForwardReference": "LarkPtxFeedForward.Reference",
    **{name: "LarkPtxMatrix" for name in MODULES[6:-1]},
    "PtxFeedForwardPipeline": "LarkPtxFeedForward.Pipeline",
}
SCOPE = (
    "Source-bound full-size compiled FP16 feed-forward development proof. Both actual "
    "parsed PTX programs (173 up-stage and 171 down-stage instructions), their prologues, "
    "all original 256/1024 reduction terms, ReLU and FP16 stores/loads, returns, all "
    "65536 up-stage and 16384 down-stage lanes and all 16384 reference outputs are covered. "
    "The actual 65536-value FP16 intermediate connects the two stateful executions. "
    "The sequential host-launch model has explicit bijective root-buffer bindings, "
    "disjoint epoch namespaces, reverse-chronological actual access traces, race freedom "
    "and a frame outside intermediate/output footprints. The independent tensor reference "
    "interprets both matmuls, ReLU and both FP16 round trips. Original shapes, dtypes, "
    "grid/block/warp and CUDA fuel [1030,1,1,1]/[4102,1,1,1] remain unchanged. "
    "Scalar operations are universally quantified. Parsing/reference formalization, "
    "logical aligned disjoint non-wrapping pointer allocations, scalar-operation "
    "correspondence and sequential host-launch correspondence remain trusted. "
    "No IEEE/error-bound, NVIDIA execution/conformance, original optimized-kernel, "
    "original model-result or paper-completion claim. This separate development checker "
    "registers no legacy SDK profile or model success."
)
VERIFIED = "verified-source-bound-full-PTX-FFN-pipeline"
sha = common.sha
read = common.read
write = common.write
manifest = common.manifest
check_inventory = common.check_inventory
fresh_output = common.fresh_output
toolchain = common.toolchain
run_lean = common.run_lean


def require(condition, message):
    if not condition:
        raise Refusal("ptx-ffn-certificate", message)


def same_json(actual, expected):
    """Reject bool/float replacements for integer metadata as well as NaNs."""
    options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
    return json.dumps(actual, **options) == json.dumps(expected, **options)


def own_sources():
    package = Path(__file__).resolve().parent
    library = pointwise.induction_path().parent
    sources = {"python/" + p.relative_to(package).as_posix(): p.read_bytes()
               for p in sorted(package.rglob("*.py"))}
    sources.update({"lean/Lark/" + name + ".lean": (library / (name + ".lean")).read_bytes()
                    for name in MODULES})
    return dict(sorted(sources.items()))


def library_tags(sources, module):
    prefix = NAMESPACES[module]
    names = re.findall(r"^#print axioms (\S+)",
                       sources["lean/Lark/" + module + ".lean"].decode(), re.M)
    return [name if name.startswith(prefix + ".") else prefix + "." + name for name in names]


def scope_fields(tasks, translations):
    return {
        "source_language": "ptx",
        "stages": [{
            "stage": stage, "reference_contract_language": task.language,
            "shapes": [list(b.shape) for b in task.buffers],
            "dtypes": [b.dtype for b in task.buffers],
            "launch": {"grid": task.grid, "block": task.block, "warp": task.warp},
            "unchanged_CUDA_contract_fuel": list(task.fuel),
            "PTX_instructions": len(translation.instructions),
        } for stage, task, translation in zip(("up", "down"), tasks, translations, strict=True)],
        "host_launch_order": ["up", "down"],
        "shared_intermediate": {"name": "hidden", "shape": [64, 1024], "dtype": "float16"},
    }


def export_bytes(inputs, output, lean):
    output = fresh_output(output)
    require(set(inputs) == set(INPUTS) and all(type(v) is bytes for v in inputs.values()),
            "Exactly both PTX programs, complete reference and unchanged contracts required")
    prepared = ptx_ffn.prepare(*(inputs[name].decode("utf-8") for name in INPUTS))
    tasks, translations, reference = prepared
    main = ptx_ffn.render(*prepared)
    sources = own_sources()
    lean, version = toolchain(lean)
    stack = list(resource.getrlimit(resource.RLIMIT_STACK))
    require(stack[0] == 8388608, "The unchanged 8 MiB stack is required")
    output.mkdir(parents=True)
    for name, content in inputs.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    (output / "Main.lean").write_text(main)
    write(output / "translation.json", [translation.data() for translation in translations])
    write(output / "reference-ast.json", reference)
    for name, content in sources.items():
        target = output / "owned-sources" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    write(output / "source-bindings.json", {name: sha(content) for name, content in sources.items()})
    report = {
        "schema": 1, "profile": ptx_ffn.PROFILE, "status": "source-build-in-progress",
        "created_at_utc": datetime.now(timezone.utc).isoformat(), "scope": SCOPE,
        **scope_fields(tasks, translations),
        "input_bindings": {name: sha(content) for name, content in inputs.items()},
        "main_sha256": sha(main.encode()),
        "reference_ast_sha256": sha((output / "reference-ast.json").read_bytes()),
        "source_bindings_sha256": sha((output / "source-bindings.json").read_bytes()),
        "lean_version": version, "lean_binary_sha256": sha(lean.read_bytes()),
        "limits": LIMITS, "original_stack_limits": stack,
        "old_owned_olean_cache_used": False, "owned_Lean_modules_freshly_compiled": 0,
        "module_checks": [], "library_axiom_audits": {},
        "source_bound_proof_accepted": False, "source_bound_development_proofs": 0,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
    }
    write(output / "results.json", report)
    modules = output / "modules"
    (modules / "Lark").mkdir(parents=True)
    environment = dict(os.environ, LEAN_PATH=str(modules), PYTHONNOUSERSITE="1")
    environment.pop("PYTHONPATH", None)
    started = time.monotonic()
    for name in MODULES:
        source = "Lark/" + name + ".lean"
        (modules / source).write_bytes(sources["lean/" + source])
        remaining = LIMITS["source_import_build_seconds"] - (time.monotonic() - started)
        require(remaining > 0, "Existing source-import aggregate limit exceeded")
        row, log = run_lean(lean, ["-o", "Lark/" + name + ".olean", source], modules,
                            environment, output / (name + ".log"), min(180, remaining))
        row["module"] = "Lark." + name
        report["module_checks"].append(row)
        write(output / "results.json", report)
        if row["exit_code"] != 0 or row["timed_out"]:
            report["status"] = "source-import-build-failed"
            write(output / "results.json", report)
            manifest(output)
            return report
        report["owned_Lean_modules_freshly_compiled"] += 1
        report["library_axiom_audits"].update(common.audits(log, library_tags(sources, name)))
        write(output / "results.json", report)
    report["import_build_seconds"] = time.monotonic() - started
    remaining = LIMITS["source_import_build_seconds"] - report["import_build_seconds"]
    require(remaining > 0, "Existing source-import aggregate limit exceeded")
    row, log = run_lean(lean, ["Main.lean"], output, environment, output / "Main.log",
                        min(180, remaining))
    report["main_check"] = row
    report["total_seconds"] = time.monotonic() - started
    accepted = row["exit_code"] == 0 and not row["timed_out"]
    if accepted:
        report["axiom_audits"] = common.audits(log, ["LarkPtxFfnCertificate." + n for n in ptx_ffn.TAGS])
    report.update(status=VERIFIED if accepted else "unproved-source-bound-PTX-FFN-pipeline",
                  source_bound_proof_accepted=accepted, source_bound_development_proofs=int(accepted))
    write(output / "results.json", report)
    manifest(output)
    return report


def expected_paths(sources):
    paths = {*INPUTS, "Main.lean", "Main.log", "translation.json", "reference-ast.json",
             "source-bindings.json", "results.json"}
    paths.update("owned-sources/" + name for name in sources)
    for name in MODULES:
        paths.update((name + ".log", "modules/Lark/" + name + ".lean", "modules/Lark/" + name + ".olean"))
    return paths


def valid_check(row, log, command):
    elapsed, timeout = row.get("seconds"), row.get("timeout_seconds")
    return (type(row.get("exit_code")) is int and row["exit_code"] == 0
            and row.get("timed_out") is False and row.get("log_sha256") == sha(log)
            and isinstance(row.get("command"), list) and row["command"][1:] == command
            and type(elapsed) in (int, float) and math.isfinite(elapsed) and elapsed >= 0
            and type(timeout) in (int, float) and math.isfinite(timeout) and 0 < timeout <= 180)


def check_export(root, output, lean):
    root, output = Path(root).resolve(), fresh_output(output)
    check_inventory(root)
    original = read(root / "results.json")
    require(original["status"] == VERIFIED and original["profile"] == ptx_ffn.PROFILE
            and original["scope"] == SCOPE and type(original["schema"]) is int and original["schema"] == 1
            and original["source_bound_proof_accepted"] is True
            and original["original_paper_fully_reproduced"] is original["nvidia_execution"] is False
            and all(type(original[k]) is int and original[k] == value for k, value in
                    {"model_calls": 0, "gpu_trials": 0, "new_registered_source_certificates": 0,
                     "source_bound_development_proofs": 1, "owned_Lean_modules_freshly_compiled": len(MODULES)}.items()),
            "Recording proof/experiment scope differs")
    sources = own_sources()
    require(set(read(root / "manifest.json")) == expected_paths(sources), "Exact export file roster differs")
    require(read(root / "source-bindings.json") == {name: sha(content) for name, content in sources.items()}
            and all((root / "owned-sources" / name).read_bytes() == content for name, content in sources.items()),
            "Current trusted SDK/library differs from captured source")
    inputs = {name: (root / name).read_bytes() for name in INPUTS}
    require(original["input_bindings"] == {name: sha(content) for name, content in inputs.items()},
            "Input bindings differ")
    prepared = ptx_ffn.prepare(*(inputs[name].decode("utf-8") for name in INPUTS))
    tasks, translations, reference = prepared
    scope = scope_fields(tasks, translations)
    require(same_json({key: original[key] for key in scope}, scope),
            "Recorded task/program/host-pipeline scope differs from actual inputs")
    main = ptx_ffn.render(*prepared).encode()
    require((root / "Main.lean").read_bytes() == main and original["main_sha256"] == sha(main)
            and same_json(read(root / "translation.json"), [t.data() for t in translations])
            and same_json(read(root / "reference-ast.json"), reference)
            and original["reference_ast_sha256"] == sha((root / "reference-ast.json").read_bytes()),
            "Main/translations/reference do not regenerate from actual input bytes")
    require(same_json(original["limits"], LIMITS) and original["old_owned_olean_cache_used"] is False
            and same_json(original["original_stack_limits"], [8388608, -1])
            and original["source_bindings_sha256"] == sha((root / "source-bindings.json").read_bytes())
            and original["lean_binary_sha256"] == LEAN_SHA256,
            "Resource/import/source/toolchain scope differs")
    main_tags = ["LarkPtxFfnCertificate." + name for name in ptx_ffn.TAGS]
    require(original["axiom_audits"] == common.audits((root / "Main.log").read_text(), main_tags),
            "Recorded Main axiom audits differ")
    checks, library = original["module_checks"], {}
    require(len(checks) == len(MODULES) and [row["module"] for row in checks] == ["Lark." + n for n in MODULES],
            "Recorded owned-module roster differs")
    for name, row in zip(MODULES, checks, strict=True):
        log = (root / (name + ".log")).read_bytes()
        require(valid_check(row, log, ["-o", "Lark/" + name + ".olean", "Lark/" + name + ".lean"])
                and (root / "modules/Lark" / (name + ".lean")).read_bytes() == sources["lean/Lark/" + name + ".lean"],
                "Recorded module kernel check/source differs")
        library.update(common.audits(log.decode(), library_tags(sources, name)))
    elapsed, total = original["import_build_seconds"], original["total_seconds"]
    require(type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 600
            and type(total) in (int, float) and math.isfinite(total) and elapsed <= total <= 600,
            "Recorded import resource scope differs")
    require(original["library_axiom_audits"] == library
            and valid_check(original["main_check"], (root / "Main.log").read_bytes(), ["Main.lean"]),
            "Recorded library/Main kernel checks differ")
    fresh = export_bytes(inputs, output, lean)
    require(fresh["source_bound_proof_accepted"] is True and (output / "Main.lean").read_bytes() == main,
            "Fresh source-only proof did not verify identically")
    (output / "manifest.json").rename(output / "proof-export-manifest.json")
    result = {
        "schema": 1, "status": "fresh-source-only-PTX-FFN-pipeline-proof-replay-passed",
        "recording_manifest_sha256": sha((root / "manifest.json").read_bytes()),
        "fresh_export_manifest_sha256": sha((output / "proof-export-manifest.json").read_bytes()),
        "main_sha256": sha(main), "main_regenerated_identically": True,
        "owned_modules_freshly_compiled": len(MODULES), "old_owned_olean_cache_used": False,
        "fresh_export_axiom_audits": fresh["axiom_audits"], "positive_rechecks": 1,
        "source_bound_proofs_added": 0, "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
        "scope": "Installed matched trusted SDK regenerates identical Main from both PTX programs, "
                 "the full independent reference and unchanged contracts. All fourteen owned modules "
                 "compile from current installed source before checking Main and standard axioms. "
                 "Captured Python/Lean/oleans are data, never executed or loaded. One existing "
                 "full pipeline development proof is rechecked; no new kernel/model/hardware result.",
    }
    write(output / "replay.json", result)
    manifest(output)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    verify = sub.add_parser("verify")
    arguments = ("up-source", "down-source", "reference", "up-contract", "down-contract")
    for name in (*arguments, "output", "lean"):
        verify.add_argument("--" + name, required=True, type=Path)
    replay = sub.add_parser("replay")
    for name in ("recording", "output", "lean"):
        replay.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    if args.action == "verify":
        inputs = {name: getattr(args, argument.replace("-", "_")).read_bytes()
                  for name, argument in zip(INPUTS, arguments, strict=True)}
        result = export_bytes(inputs, args.output, args.lean)
        if not result.get("source_bound_proof_accepted"):
            raise SystemExit(1)
    else:
        result = check_export(args.recording, args.output, args.lean)
    print(json.dumps({"status": result["status"]}))


if __name__ == "__main__":
    main()
