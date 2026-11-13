"""Prepare the seventeen owned CUDA proof tasks without CUDA hardware or inference.

Existing CUDA sources/tasks retain their shapes, fuels and native warp width.
SDK proofs are preparation controls, never model-generated successes.
"""

import argparse
import importlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.local_models import full_shape as shared  # noqa: E402


def cuda_cases():
    result = []
    for name, module, directory in shared.benchmark.CASES:
        parts = Path(directory).parts
        shared.require(parts.count("hip") == 1, "Ambiguous benchmark backend directory")
        directory = str(Path(*("cuda" if part == "hip" else part for part in parts)))
        shared.require((ROOT / "reproduction" / directory).is_dir(), "Missing CUDA fixture")
        result.append((name, module, directory))
    return result


def sdk_case(case):
    _, module, directory = case
    shared.require("cuda" in Path(directory).parts and "hip" not in Path(directory).parts,
                   "A CUDA case directory is required")
    folder = ROOT / "reproduction" / directory
    owned = {p.name: p.read_bytes() for p in folder.iterdir() if p.is_file()}
    shared.require(not any(name.endswith(".hip") for name in owned), "Mixed source backends")
    tasks = [json.loads(b) for n, b in owned.items() if n.endswith("task.json")]
    shared.require(tasks and all(t["language"] == "cuda" and t["launch"]["warp"] == 32
                                 for t in tasks), "CUDA task/native warp identity differs")
    sdk = importlib.import_module("lark_kernels." + module)
    if module == "feedforward":
        args = sdk.prepare(*(owned[n].decode() for n in (
            "up.cu", "down.cu", "reference.py", "up-task.json", "down-task.json")))
    elif module in ("attention", "swiglu"):
        args = sdk.prepare({n: b.decode() for n, b in owned.items()})
    else:
        args = sdk.prepare(*(owned[n].decode() for n in ("kernel.cu", "reference.py", "task.json")))
    rendered = sdk.render(*args)
    block = rendered[rendered.rindex("namespace LarkCertificate"):]
    block = re.sub(r"(?m)^set_option (?:maxRecDepth|maxHeartbeats) [0-9]+\s*$", "", block)
    shared.require("set_option" not in block, "Unexpected SDK certificate option")
    return block, {str((folder / n).relative_to(ROOT)): b for n, b in owned.items()}


def prepare(output, lean):
    shared.require(not any((p / ".git").exists() for p in (output, *output.parents)),
                   "Preparation outputs must be outside Git")
    output.mkdir(parents=True, exist_ok=False)
    selected = cuda_cases()
    libraries = shared.benchmark.reference_libraries(shared.references)
    bindings = shared.freeze_sources(output, selected, libraries)
    name = "reproduction/local_models/cuda_shape.py"
    content = Path(__file__).read_bytes()
    (output / "source" / name).write_bytes(content)
    bindings[name] = shared.digest(content)
    bindings = dict(sorted(bindings.items()))
    shared.write(output / "source-manifest.json", bindings)
    version = subprocess.check_output([str(lean), "--version"], text=True, timeout=30).strip()
    shared.require(version.startswith("Lean (version 4.19.0,"), "Lean 4.19.0 is required")
    report = {
        "schema": 1, "status": "full-shape-fixture-preparation-in-progress",
        "protocol": "full-shape-four-slots-v1", "language": "cuda", "native_warp": 32,
        "lean_version": version, "lean_binary_sha256": shared.digest(lean.read_bytes()),
        "source_manifest_sha256": shared.digest((output / "source-manifest.json").read_bytes()),
        "source_files": len(bindings), "limits": shared.LIMITS,
        "proof_slots": list(shared.SLOTS), "model_calls": 0, "gpu_trials": 0,
        "new_certificates": 0, "original_paper_fully_reproduced": False, "cases": [],
        "scope": "Independent CUDA source-bound proof preparation at existing full shapes/warp32/fuels. SDK positive controls are not model proofs. No CUDA execution or NVIDIA hardware validation.",
    }
    shared.write(output / "results.json", report)
    cache, environment = shared.real_backend.prepare(libraries, str(lean), 600, target=shared.TARGET)
    marker = json.loads((cache / "checked-build.json").read_text())
    shared.write(output / "imports.json", {
        "target": shared.TARGET, "source_checked_cache": str(cache),
        "sources": marker["sources"], "compiled": marker["compiled"],
        "sdk_import_cache_reused_or_source_checked": True,
        "cold_rebuild_of_all_imports_claimed": False,
    })
    catalogue = {n: {"bytes": len(b), "sha256": shared.digest(b)}
                 for n, b in sorted(libraries.items())}
    for case in selected:
        name = case[0]
        folder = output / "cases" / name
        folder.mkdir(parents=True)
        block, owned = sdk_case(case)
        spans = shared.proof_spans(block)
        known = {n: spans[n]["sdk_positive_control"] for n in shared.SLOTS}
        masked = {n: "by fail" for n in shared.SLOTS}
        (folder / "sdk-block.lean.txt").write_text(block)
        shared.write(folder / "source-bindings.json", {
            n: shared.digest(b) for n, b in sorted(owned.items())})
        request = {
            "schema": 1, "case": name, "language": "cuda", "native_warp": 32,
            "proof_slots": list(shared.SLOTS), "immutable_main": shared.render(block, masked),
            "limits": shared.LIMITS, "theorem_types": {n: spans[n]["type"] for n in shared.SLOTS},
            "source_files": {n: b.decode() for n, b in sorted(owned.items())},
            "available_lean_library_sources": catalogue, "sdk_tactic_bodies_included": False,
            "scope": "Full-size independent CUDA source; four fixed proof slots; abstract scalar operations; no original-paper registry or NVIDIA measurements.",
        }
        shared.write(folder / "request.json", request)
        row = {"case": name, "request_sha256": shared.digest((folder / "request.json").read_bytes()),
               "source_bindings_sha256": shared.digest((folder / "source-bindings.json").read_bytes())}
        for label, proofs, expected in (("sdk-positive", known, True),
                                         ("all-masked-negative", masked, False)):
            destination = folder / label
            destination.mkdir()
            (destination / "Main.lean").write_text(shared.render(block, proofs))
            ok, log = shared.certificate.run_lean(destination, str(lean), 180, env=environment)
            (destination / "lean.log").write_text(log)
            shared.require(ok is expected and "Lean timed out" not in log,
                           "Unexpected CUDA preparation outcome: " + name + "/" + label)
            shared.require(expected or "tactic 'fail' failed" in log,
                           "Masked CUDA fixture failed outside its proof hole: " + name)
            row[label] = {"accepted": ok, "main_sha256": shared.digest((destination / "Main.lean").read_bytes()),
                          "lean_log_sha256": shared.digest(log.encode())}
        report["cases"].append(row)
        shared.write(output / "results.json", report)
        print(json.dumps({"case": name, "language": "cuda", "sdk_positive": True,
                          "masked_negative_rejected": True}), flush=True)
    report.update(status="full-shape-model-fixtures-prepared-and-baselines-checked",
                  positive_lean_checks=len(selected), masked_negative_lean_checks=len(selected))
    shared.write(output / "results.json", report)
    shared.write(output / "manifest.json", {
        str(p.relative_to(output)): shared.digest(p.read_bytes())
        for p in sorted(output.rglob("*")) if p.is_file()})
    print(json.dumps({"status": report["status"], "language": "cuda",
                      "positive_lean_checks": len(selected), "masked_negative_lean_checks": len(selected),
                      "model_calls": 0, "gpu_trials": 0}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--lean", required=True, type=Path)
    args = parser.parse_args()
    lean = Path(shared.certificate.lean_binary(str(args.lean)))
    prepare(args.output.resolve(), lean)


if __name__ == "__main__":
    main()
