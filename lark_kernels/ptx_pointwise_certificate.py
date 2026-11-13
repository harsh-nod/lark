"""Export/recheck the finite FP16 PTX profile without executing captured Python.

The supported path uses an unchanged scalar CUDA reference contract alongside
the actual generated PTX source. This is a separate development checker; it is
not the old bounded PTX profile or a reproduction of the original paper's runs.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import time

from . import certificate, pointwise, ptx_pointwise
from .ir import Refusal

INPUTS = ("kernel.ptx", "reference.py", "contract.json")
PYTHON_SOURCES = ("__init__.py", "ptx_pointwise.py", "ptx_pointwise_certificate.py",
                  "pointwise.py", "ptx.py", "frontend.py", "ir.py", "spec.py",
                  "certificate.py")
LIMITS = {"maxRecDepth": 10000, "maxHeartbeats": 2000000,
          "per_Lean_process_seconds": 180, "source_import_build_seconds": 600}
LEAN_SHA256 = "92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023"
SCOPE = (
    "Direct source-bound finite PTX FP16 pointwise proof against the closed reference AST. "
    "Every parsed instruction executes in the declared abstract model; all grid blocks, "
    "actual memory-event race freedom and every reference output are covered. "
    "The original scalar CUDA contract, shapes, dtypes, geometry and CUDA fuel remain "
    "unchanged. PTX execution is structurally finite and consumes every instruction; "
    "the CUDA fuel is data for its separate model, not a bound of four PTX instructions. "
    "Python parsing/reference formalization, pointer provenance, aligned disjoint "
    "non-wrapping allocations and scalar-operation correspondence remain trusted. "
    "No IEEE/error-bound, NVIDIA execution/conformance, original optimized kernel or "
    "original model-result claim. This separate development checker registers no new "
    "legacy SDK profile or model success."
)


def require(ok, message):
    if not ok:
        raise Refusal("ptx-pointwise-certificate", message)


def sha(content):
    return hashlib.sha256(content).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def safe_name(name):
    path = PurePosixPath(name)
    return bool(name) and not path.is_absolute() and str(path) == name and not {
        ".", ".."
    } & set(path.parts)


def own_sources():
    python = Path(__file__).resolve().parent
    library = pointwise.induction_path().parent
    sources = {"python/" + name: (python / name).read_bytes() for name in PYTHON_SOURCES}
    sources.update({"lean/Lark/" + name: (library / name).read_bytes()
                    for name in ("Nonlinear.lean", "Pointwise.lean", "PtxPointwise.lean")})
    return dict(sorted(sources.items()))


def audits(log, tags):
    require("sorry" not in log and "error:" not in log, "Lean error or unproved axiom")
    result = {}
    for tag in tags:
        no = re.findall("^" + re.escape("'" + tag + "' does not depend on any axioms")
                        + r"\s*$", log, re.M)
        dep = re.findall("^" + re.escape("'" + tag + "' depends on axioms:")
                         + r"\s*\[([^]]*)\]", log, re.M)
        require(len(no) + len(dep) == 1, "Missing/ambiguous axiom audit: " + tag)
        values = {v.strip() for v in dep[0].split(",") if v.strip()} if dep else set()
        require(values <= certificate.AXIOMS, "Nonstandard axiom: " + tag)
        result[tag] = sorted(values)
    return result


def manifest(root):
    write(root / "manifest.json", {str(p.relative_to(root)): sha(p.read_bytes())
                                  for p in sorted(root.rglob("*")) if p.is_file()
                                  and p != root / "manifest.json"})


def check_inventory(root):
    expected = read(root / "manifest.json")
    require(isinstance(expected, dict) and all(safe_name(n) for n in expected),
            "Unsafe recording inventory")
    require(not any(p.is_symlink() for p in root.rglob("*")), "Recording symlink")
    require({str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
            == set(expected) | {"manifest.json"}, "Recording inventory differs")
    require(all(sha((root / name).read_bytes()) == value for name, value in expected.items()),
            "Recording bytes differ")


def run_lean(lean, command, cwd, environment, log, timeout=180):
    start = time.monotonic()
    try:
        result = subprocess.run([str(lean), *command], cwd=cwd, env=environment,
                                text=True, capture_output=True, timeout=timeout)
        content = result.stdout + result.stderr
        row = {"exit_code": result.returncode, "timed_out": False}
    except subprocess.TimeoutExpired as error:
        def text(value):
            return value.decode() if isinstance(value, bytes) else value or ""
        content = text(error.stdout) + text(error.stderr) + "\nLean process timed out.\n"
        row = {"exit_code": None, "timed_out": True}
    log.write_text(content)
    row.update(seconds=time.monotonic() - start, log_sha256=sha(content.encode()),
               command=[str(lean), *command], timeout_seconds=timeout)
    return row, content


def fresh_output(output):
    output = Path(output).resolve()
    require(not output.exists() and not any((p / ".git").exists()
            for p in (output, *output.parents)), "Fresh output outside Git required")
    return output


def toolchain(lean):
    # Keep an elan shim's basename: resolving its symlink before invocation
    # would invoke elan rather than its lean subcommand.
    supplied = Path(lean).absolute()
    prefix = subprocess.check_output([str(supplied), "--print-prefix"],
                                     text=True, timeout=30).strip()
    actual = (Path(prefix) / "bin/lean").resolve()
    require(actual.is_file() and sha(actual.read_bytes()) == LEAN_SHA256,
            "Pinned Linux x86_64 Lean4.19.0 release binary required")
    version = subprocess.check_output([str(actual), "--version"], text=True, timeout=30).strip()
    require(version.startswith("Lean (version 4.19.0,"), "Lean 4.19.0 required")
    return actual, version


def export_bytes(inputs, output, lean):
    output = fresh_output(output)
    require(set(inputs) == set(INPUTS) and all(isinstance(v, bytes) for v in inputs.values()),
            "Exactly PTX, reference and unchanged contract bytes required")
    args = ptx_pointwise.prepare(*(inputs[name].decode() for name in INPUTS))
    task, translation, _ = args
    main = ptx_pointwise.render(*args)
    sources = own_sources()
    lean, version = toolchain(lean)
    output.mkdir(parents=True)
    for name, content in inputs.items():
        (output / name).write_bytes(content)
    (output / "Main.lean").write_text(main)
    write(output / "translation.json", translation.data())
    for name, content in sources.items():
        target = output / "owned-sources" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    bindings = {name: sha(content) for name, content in sources.items()}
    write(output / "source-bindings.json", bindings)
    report = {
        "schema": 1, "profile": ptx_pointwise.PROFILE, "status": "in-progress",
        "created_at_utc": datetime.now(timezone.utc).isoformat(), "scope": SCOPE,
        "source_language": "ptx", "reference_contract_language": task.language,
        "elements": task.buffers[0].size,
        "launch": {"grid": task.grid, "block": task.block, "warp": task.warp},
        "unchanged_CUDA_contract_fuel": list(task.fuel),
        "PTX_instructions": len(translation.instructions),
        "input_bindings": {name: sha(value) for name, value in inputs.items()},
        "main_sha256": sha(main.encode()),
        "source_bindings_sha256": sha((output / "source-bindings.json").read_bytes()),
        "lean_version": version, "lean_binary_sha256": sha(lean.read_bytes()),
        "limits": LIMITS, "old_owned_olean_cache_used": False,
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "new_registered_source_certificates": 0,
        "original_paper_fully_reproduced": False, "module_checks": [],
    }
    write(output / "results.json", report)
    modules = output / "modules"
    (modules / "Lark").mkdir(parents=True)
    environment = os.environ.copy()
    environment["LEAN_PATH"] = str(modules)
    import_started = time.monotonic()
    for name in ("Nonlinear", "Pointwise", "PtxPointwise"):
        source_name = "Lark/" + name + ".lean"
        (modules / source_name).write_bytes(sources["lean/" + source_name])
        remaining = 600 - (time.monotonic() - import_started)
        require(remaining > 0, "Source import build exceeded existing600second limit")
        row, log = run_lean(lean, ["-o", "Lark/" + name + ".olean", source_name],
                            modules, environment, output / (name + ".log"), min(180, remaining))
        row["module"] = "Lark." + name
        report["module_checks"].append(row)
        write(output / "results.json", report)
        if row["exit_code"] != 0 or row["timed_out"]:
            report["status"] = "source-import-build-failed"
            write(output / "results.json", report)
            manifest(output)
            return report
        if name == "PtxPointwise":
            tags = re.findall(r"^#print axioms (\S+)", sources["lean/" + source_name].decode(), re.M)
            require(len(tags) == 22, "Generic-library audit roster differs")
            report["library_axiom_audits"] = audits(log, tags)
    row, log = run_lean(lean, ["Main.lean"], output, environment, output / "Main.log")
    report["main_check"] = row
    accepted = row["exit_code"] == 0 and not row["timed_out"]
    if accepted:
        report["axiom_audits"] = audits(log, ["LarkPtxCertificate." + n for n in ptx_pointwise.TAGS])
    report.update(status="verified-source-bound-finite-PTX" if accepted else "unproved-source-bound-PTX",
                  source_bound_proof_accepted=accepted,
                  owned_Lean_modules_freshly_compiled=3,
                  import_build_seconds=time.monotonic() - import_started - row["seconds"])
    write(output / "results.json", report)
    manifest(output)
    return report


def check_export(root, output, lean):
    root = Path(root).resolve()
    output = fresh_output(output)
    check_inventory(root)
    original = read(root / "results.json")
    require(original["status"] == "verified-source-bound-finite-PTX"
            and original["source_bound_proof_accepted"] is True
            and original["profile"] == ptx_pointwise.PROFILE and original["scope"] == SCOPE
            and original["original_paper_fully_reproduced"] is False
            and original["nvidia_execution"] is False
            and all(type(original[k]) is int and original[k] == 0 for k in
                    ("model_calls", "gpu_trials", "new_registered_source_certificates")),
            "Recording proof/experiment scope differs")
    expected = own_sources()
    require(read(root / "source-bindings.json") ==
            {name: sha(content) for name, content in expected.items()},
            "Current trusted checker/library differs from recorded source")
    require(all((root / "owned-sources" / name).read_bytes() == content
                for name, content in expected.items()), "Captured owned source differs")
    inputs = {name: (root / name).read_bytes() for name in INPUTS}
    require(original["input_bindings"] == {name: sha(v) for name, v in inputs.items()},
            "Input bindings differ")
    args = ptx_pointwise.prepare(*(inputs[name].decode() for name in INPUTS))
    task, translation, _ = args
    require(original["elements"] == task.buffers[0].size
            and type(original["elements"]) is int
            and original["launch"] == {"grid": task.grid, "block": task.block, "warp": task.warp}
            and original["source_language"] == "ptx"
            and original["reference_contract_language"] == task.language
            and original["unchanged_CUDA_contract_fuel"] == list(task.fuel)
            and type(original["PTX_instructions"]) is int
            and original["PTX_instructions"] == len(translation.instructions),
            "Recorded task/program scope differs from actual inputs")
    main = ptx_pointwise.render(*args).encode()
    require((root / "Main.lean").read_bytes() == main and original["main_sha256"] == sha(main)
            and read(root / "translation.json") == args[1].data(),
            "Main/translation does not regenerate from actual source/reference/contract")
    require(original["limits"] == LIMITS and original["old_owned_olean_cache_used"] is False
            and original["owned_Lean_modules_freshly_compiled"] == 3,
            "Resource/import scope differs")
    require(original["source_bindings_sha256"] == sha((root / "source-bindings.json").read_bytes())
            and original["lean_binary_sha256"] == LEAN_SHA256,
            "Recorded source/toolchain binding differs")
    main_tags = ["LarkPtxCertificate." + n for n in ptx_pointwise.TAGS]
    require(original["axiom_audits"] == audits((root / "Main.log").read_text(), main_tags),
            "Recorded Main axiom audits differ")
    library_tags = re.findall(r"^#print axioms (\S+)",
                             expected["lean/Lark/PtxPointwise.lean"].decode(), re.M)
    require(original["library_axiom_audits"] ==
            audits((root / "PtxPointwise.log").read_text(), library_tags),
            "Recorded generic-library axiom audits differ")
    require(len(original["module_checks"]) == 3 and
            [r["module"] for r in original["module_checks"]] ==
            ["Lark.Nonlinear", "Lark.Pointwise", "Lark.PtxPointwise"] and
            all(r["exit_code"] == 0 and r["timed_out"] is False
                and r["log_sha256"] == sha((root / (r["module"].split(".")[-1] + ".log")).read_bytes())
                for r in original["module_checks"])
            and original["main_check"]["exit_code"] == 0
            and original["main_check"]["timed_out"] is False
            and original["main_check"]["log_sha256"] == sha((root / "Main.log").read_bytes()),
            "Recorded module/Main kernel checks differ")
    fresh = export_bytes(inputs, output, lean)
    require(fresh["status"] == "verified-source-bound-finite-PTX",
            "Fresh source-only proof did not verify")
    require((output / "Main.lean").read_bytes() == main, "Fresh Main bytes differ")
    (output / "manifest.json").rename(output / "proof-export-manifest.json")
    result = {
        "schema": 1, "status": "fresh-source-only-PTX-proof-replay-passed",
        "recording_manifest_sha256": sha((root / "manifest.json").read_bytes()),
        "fresh_export_manifest_sha256": sha((output / "proof-export-manifest.json").read_bytes()),
        "main_sha256": sha(main), "main_regenerated_identically": True,
        "owned_modules_freshly_compiled": 3, "old_owned_olean_cache_used": False,
        "fresh_export_axiom_audits": fresh["axiom_audits"],
        "model_calls": 0, "gpu_trials": 0, "nvidia_execution": False,
        "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
        "scope": "Exact-source regeneration and three fresh owned-module compilations followed "
                 "by a new kernel/axiom check. Captured Python/Lean/oleans are data; trusted "
                 "current source identities must match before fresh compilation. The Lean "
                 "standard library comes from the checked toolchain. No NVIDIA experiment.",
    }
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
        print(json.dumps({"status": result["status"], "elements": result["elements"]}))
        if not result.get("source_bound_proof_accepted"):
            raise SystemExit(1)
    else:
        result = check_export(args.recording, args.output, args.lean)
        print(json.dumps({"status": result["status"]}))


if __name__ == "__main__":
    main()
