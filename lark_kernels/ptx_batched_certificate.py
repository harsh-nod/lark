"""Export and replay the complete compiled FP16 batched GEMM development proof.

Replay uses the installed trusted checker and fresh owned Lean modules. Captured
Python, Lean and compiled objects are inventory-bound data, never replay code.
"""

import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import re
import time

from . import pointwise, ptx_batched
from . import ptx_pointwise_certificate as common
from .ir import Refusal

INPUTS = common.INPUTS
LIMITS = dict(common.LIMITS)
LEAN_SHA256 = common.LEAN_SHA256
MODULES = ("Nonlinear", "Pointwise", "PtxPointwise", "PtxDot", "PtxMatrix", "PtxBatched", "PtxBatchedInit", "PtxBatchedBody")
NAMESPACES = dict(zip(MODULES, ("LarkNonlinear", "LarkPointwise", "LarkPtxPointwise", "LarkPtxDot", "LarkPtxMatrix", "LarkPtxBatched", "LarkPtxBatched.Bmm.Init", "LarkPtxBatched.Bmm.Body"), strict=True))
SCOPE = (
    "Source-bound complete compiled 32-batch [32,64,256] times [32,256,512] FP16 BMM "
    "development proof. All 138 actual parsed instructions, the 29-instruction prologue, "
    "98-instruction body, all 16 iterations of the real sixteen-term backward loop, five "
    "control instructions, epilogue and ret, all 1048576 active lanes, actual access-trace "
    "race freedom, every extracted closed batched reference output and preservation outside "
    "the output footprint are covered under the declared abstract scalar interpretation. "
    "The unchanged CUDA shapes/dtypes, grid 1048576/block 1/warp 32 and fuel [1030,1,1,1] "
    "are retained. Finite PTX execution is an inductive sequence of actual successful "
    "transitions; CUDA fuel remains separate data, with no new execution fuel. Python "
    "parsing/reference formalization, logical pointer provenance, aligned disjoint "
    "non-wrapping allocations and scalar-operation correspondence remain trusted. "
    "No IEEE/error-bound, PyTorch/NVIDIA hardware-conformance, original optimized kernel, "
    "original model-result or original-paper-completion claim. This separate development "
    "checker registers no legacy SDK profile or model success."
)
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
        raise Refusal("ptx-batched-certificate", message)


def same_json(actual, expected):
    """Keep JSON booleans and floating-point counters distinct from integers."""
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
    namespace = NAMESPACES[module]
    names = re.findall(r"^#print axioms (\S+)", sources["lean/Lark/" + module + ".lean"].decode(), re.M)
    return [name if name.startswith(namespace + ".") else namespace + "." + name for name in names]


def scope_fields(task, translation):
    return {"source_language": "ptx", "reference_contract_language": task.language,
            "shapes": [list(b.shape) for b in task.buffers],
            "dtypes": [b.dtype for b in task.buffers],
            "launch": {"grid": task.grid, "block": task.block, "warp": task.warp},
            "unchanged_CUDA_contract_fuel": list(task.fuel),
            "PTX_instructions": len(translation.instructions)}


def export_bytes(inputs, output, lean):
    output = fresh_output(output)
    require(set(inputs) == set(INPUTS) and all(type(v) is bytes for v in inputs.values()),
            "Exactly PTX, reference and unchanged contract bytes required")
    prepared = ptx_batched.prepare_certificate(*(inputs[name].decode() for name in INPUTS))
    task, translation, reference = prepared
    main = ptx_batched.render(*prepared)
    sources = own_sources()
    lean, version = toolchain(lean)
    output.mkdir(parents=True)
    for name, content in inputs.items():
        (output / name).write_bytes(content)
    (output / "Main.lean").write_text(main)
    write(output / "translation.json", translation.data())
    write(output / "reference-ast.json", reference)
    for name, content in sources.items():
        target = output / "owned-sources" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    write(output / "source-bindings.json", {name: sha(content) for name, content in sources.items()})
    report = {
        "schema": 1, "profile": ptx_batched.PROFILE, "status": "source-build-in-progress",
        "created_at_utc": datetime.now(timezone.utc).isoformat(), "scope": SCOPE,
        **scope_fields(task, translation), "input_bindings": {n: sha(v) for n, v in inputs.items()},
        "main_sha256": sha(main.encode()), "reference_ast_sha256": sha((output / "reference-ast.json").read_bytes()),
        "source_bindings_sha256": sha((output / "source-bindings.json").read_bytes()),
        "lean_version": version, "lean_binary_sha256": sha(lean.read_bytes()),
        "limits": LIMITS, "old_owned_olean_cache_used": False,
        "owned_Lean_modules_freshly_compiled": 0, "module_checks": [], "library_axiom_audits": {},
        "source_bound_proof_accepted": False, "source_bound_development_proofs": 0,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
    }
    write(output / "results.json", report)
    modules = output / "modules"
    (modules / "Lark").mkdir(parents=True)
    environment = dict(os.environ, LEAN_PATH=str(modules))
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
    row, log = run_lean(lean, ["Main.lean"], output, environment, output / "Main.log")
    report["main_check"] = row
    accepted = row["exit_code"] == 0 and not row["timed_out"]
    if accepted:
        report["axiom_audits"] = common.audits(log, ["LarkPtxBatchedCertificate." + n for n in ptx_batched.TAGS])
    report.update(status="verified-source-bound-full-PTX-BMM" if accepted else "unproved-source-bound-PTX-BMM",
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
    elapsed = row.get("seconds")
    timeout = row.get("timeout_seconds")
    return (type(row.get("exit_code")) is int and row["exit_code"] == 0
            and row.get("timed_out") is False and row.get("log_sha256") == sha(log)
            and isinstance(row.get("command"), list) and row["command"][1:] == command
            and type(elapsed) in (int, float) and math.isfinite(elapsed) and elapsed >= 0
            and type(timeout) in (int, float) and math.isfinite(timeout) and 0 < timeout <= 180)


def check_export(root, output, lean):
    root, output = Path(root).resolve(), fresh_output(output)
    check_inventory(root)
    original = read(root / "results.json")
    require(original["status"] == "verified-source-bound-full-PTX-BMM"
            and original["profile"] == ptx_batched.PROFILE and original["scope"] == SCOPE
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
    require(original["input_bindings"] == {n: sha(v) for n, v in inputs.items()}, "Input bindings differ")
    prepared = ptx_batched.prepare_certificate(*(inputs[name].decode() for name in INPUTS))
    task, translation, reference = prepared
    require(same_json({k: original[k] for k in scope_fields(task, translation)}, scope_fields(task, translation)),
            "Recorded task/program scope differs from actual inputs")
    main = ptx_batched.render(*prepared).encode()
    require((root / "Main.lean").read_bytes() == main and original["main_sha256"] == sha(main)
            and same_json(read(root / "translation.json"), translation.data())
            and same_json(read(root / "reference-ast.json"), reference)
            and original["reference_ast_sha256"] == sha((root / "reference-ast.json").read_bytes()),
            "Main/translation/reference does not regenerate from actual input bytes")
    require(same_json(original["limits"], LIMITS) and original["old_owned_olean_cache_used"] is False
            and original["source_bindings_sha256"] == sha((root / "source-bindings.json").read_bytes())
            and original["lean_binary_sha256"] == LEAN_SHA256,
            "Resource/import/source/toolchain scope differs")
    main_tags = ["LarkPtxBatchedCertificate." + name for name in ptx_batched.TAGS]
    require(original["axiom_audits"] == common.audits((root / "Main.log").read_text(), main_tags),
            "Recorded Main axiom audits differ")
    library = {}
    checks = original["module_checks"]
    require(len(checks) == len(MODULES) and [r["module"] for r in checks] == ["Lark." + n for n in MODULES],
            "Recorded owned-module roster differs")
    for name, row in zip(MODULES, checks, strict=True):
        log = (root / (name + ".log")).read_bytes()
        require(valid_check(row, log, ["-o", "Lark/" + name + ".olean", "Lark/" + name + ".lean"])
                and (root / "modules/Lark" / (name + ".lean")).read_bytes() == sources["lean/Lark/" + name + ".lean"],
                "Recorded module kernel check/source differs")
        library.update(common.audits(log.decode(), library_tags(sources, name)))
    elapsed = original["import_build_seconds"]
    require(type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 600,
            "Recorded import resource scope differs")
    require(original["library_axiom_audits"] == library
            and valid_check(original["main_check"], (root / "Main.log").read_bytes(), ["Main.lean"]),
            "Recorded library/Main kernel checks differ")
    fresh = export_bytes(inputs, output, lean)
    require(fresh["source_bound_proof_accepted"] is True and (output / "Main.lean").read_bytes() == main,
            "Fresh source-only proof did not verify identically")
    (output / "manifest.json").rename(output / "proof-export-manifest.json")
    result = {"schema": 1, "status": "fresh-source-only-PTX-BMM-proof-replay-passed",
              "recording_manifest_sha256": sha((root / "manifest.json").read_bytes()),
              "fresh_export_manifest_sha256": sha((output / "proof-export-manifest.json").read_bytes()),
              "main_sha256": sha(main), "main_regenerated_identically": True,
              "owned_modules_freshly_compiled": len(MODULES), "old_owned_olean_cache_used": False,
              "fresh_export_axiom_audits": fresh["axiom_audits"], "positive_rechecks": 1,
              "source_bound_proofs_added": 0, "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
              "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
              "scope": "Installed trusted SDK regenerates the identical Main from captured inputs and "
                       "compiles all eight owned modules from current matched source, then rechecks the "
                       "kernel and axioms. Captured Python/Lean/oleans are data and are not executed/loaded. "
                       "One existing development proof is rechecked, not a new kernel or NVIDIA experiment."}
    write(output / "replay.json", result)
    manifest(output)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    verify = sub.add_parser("verify")
    for name in ("source", "reference", "contract", "output", "lean"):
        verify.add_argument("--" + name, required=True, type=Path)
    replay = sub.add_parser("replay")
    for name in ("recording", "output", "lean"):
        replay.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    if args.action == "verify":
        inputs = {name: path.read_bytes() for name, path in
                  zip(INPUTS, (args.source, args.reference, args.contract), strict=True)}
        result = export_bytes(inputs, args.output, args.lean)
        if not result.get("source_bound_proof_accepted"):
            raise SystemExit(1)
    else:
        result = check_export(args.recording, args.output, args.lean)
    print(json.dumps({"status": result["status"]}))


if __name__ == "__main__":
    main()
