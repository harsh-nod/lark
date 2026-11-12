"""Replay frozen FlashInfer RMSNorm first-block execution without Git or owned caches."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_metadata(report):
    required = {
        "schema": 1, "status": "native-flashinfer-rmsnorm-first-block-execution-checked",
        "local_lean_modules": 30, "library_axiom_audits": 225, "source_instances": 6,
        "source_axiom_audits_per_instance": 12, "false_lean_claims_rejected": 11,
        "full_source_binding_proved": True,
        "address_coverage_and_native_ownership_proved": True,
        "conditional_footprint_race_freedom_proved": True,
        "first_block_scheduler_execution_proved": True,
        "first_block_partial_values_proved": True,
        "first_block_readonly_input_preservation_proved": True,
        "first_block_actual_trace_race_freedom_proved": True,
        "first_barrier_continuation_proved": True,
        "first_block_actual_trace_classification_proved": True,
        "second_reduction_execution_proved": False, "normalized_output_proved": False,
        "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
        "source_reference_equality_proved": False, "source_certificates": 0,
        "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    extra = {"axiom_audits", "checks", "source_archive_sha256", "source_manifest_sha256"}
    if (set(report) != set(required) | extra
            or any(type(report.get(k)) is not type(v) or report[k] != v for k, v in required.items())):
        raise ValueError("Unsupported native FlashInfer RMSNorm stage/scope metadata")
    audits = report["axiom_audits"]
    if len(audits) != 7 or len(audits["fresh-build"]) != 225:
        raise ValueError("Principal audit coverage differs")
    for name, values in audits.items():
        if (name != "fresh-build" and len(values) != 12
                or any(not set(v) <= {"propext", "Classical.choice", "Quot.sound"} for v in values.values())):
            raise ValueError("Axiom closure differs")
    principals = {"LarkNativeFlashInferRmsNorm." + name for name in (
        "first_block_fold_run", "first_block_partial", "first_block_cells",
        "first_block_good", "first_block_cut", "first_block_initial_run",
        "first_block_initial_race_free", "initial_first_barrier", "initial_mid_ready")}
    if not principals <= set(audits["fresh-build"]):
        raise ValueError("Missing conditional race-freedom principal")
    if any(not {"source_binding", "source_conditional_race_free", "source_first_block_run",
                    "source_first_block_partials", "source_first_block_inputs", "source_first_block_race_free",
                    "source_first_barrier_continuation", "source_first_barrier_epoch", "source_first_barrier_pc"} <= set(values)
           for name, values in audits.items() if name != "fresh-build"):
        raise ValueError("Missing source-binding principal")
    names = ["fresh-build"] + ["rows_" + str(rows) for rows in (1, 3, 64, 255, 65535, 131072)]
    names += ["wrong-reduction-mask", "wrong-logical-width", "removed-first-barrier",
              "removed-second-barrier", "wrong-weight-index", "aliased-output",
              "wrong-mean", "missing-store", "denied-output-owner",
              "wrong-first-barrier-pc", "wrong-first-xor-pc"]
    checks = report["checks"]
    if (len(checks) != len(names) or [c["name"] for c in checks] != names
            or any(c["accepted"] is not (i < 7) or type(c["exit_code"]) is not int
                   or c["exit_code"] != (0 if i < 7 else 1) for i, c in enumerate(checks))):
        raise ValueError("Incomplete FlashInfer RMSNorm source/control coverage")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    manifest = json.loads((packet / "manifest.json").read_text())
    for name, expected in manifest.items():
        path = packet / name
        if not path.resolve().is_relative_to(packet) or path.is_symlink() or sha(path) != expected:
            raise ValueError("Packet binding differs: " + name)
    report = json.loads((packet / "results.json").read_text())
    validate_metadata(report)
    if (sha(packet / "source.tar.gz") != report["source_archive_sha256"]
            or sha(packet / "source-manifest.json") != report["source_manifest_sha256"]):
        raise ValueError("Source binding differs")
    out.mkdir(parents=True, exist_ok=False)
    source = out / "source"
    source.mkdir()
    hashes = json.loads((packet / "source-manifest.json").read_text())
    extracted = set()
    with tarfile.open(packet / "source.tar.gz") as archive:
        for entry in archive:
            path = PurePosixPath(entry.name)
            if (not entry.isfile() or entry.size > 10_000_000 or path.is_absolute()
                    or ".." in path.parts or str(path) != entry.name or entry.name in extracted
                    or entry.name not in hashes or ".lake" in path.parts or entry.name.endswith((".olean", ".ilean"))):
                raise ValueError("Unexpected source archive entry")
            content = archive.extractfile(entry).read()
            if hashlib.sha256(content).hexdigest() != hashes[entry.name]:
                raise ValueError("Frozen source differs")
            dest = source / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(content)
            extracted.add(entry.name)
    if extracted != set(hashes):
        raise ValueError("Incomplete source archive")
    bin_dir = out / "bin"
    bin_dir.mkdir()
    for name in ("lean", "lake"):
        (bin_dir / name).symlink_to(lean_bin / name)
    env = dict(os.environ)
    env["PATH"], env["PYTHONNOUSERSITE"] = str(bin_dir), "1"
    env.pop("PYTHONPATH", None)
    if shutil.which("git", path=env["PATH"]) is not None:
        raise ValueError("Git unexpectedly available")
    version = subprocess.check_output([str(bin_dir / "lean"), "--version"], env=env, text=True)
    if "version 4.19.0" not in version:
        raise ValueError("Pinned Lean4.19.0 required")
    run = subprocess.run([sys.executable, str(source / "reproduction/production_flashinfer_rmsnorm/check_execution.py"),
                          "--output", str(out / "fresh"), "--lean-bin", str(bin_dir)], cwd=source, env=env,
                         capture_output=True, text=True, timeout=600)
    (out / "replay.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError("Frozen first-block execution replay failed: " + run.stdout + run.stderr)
    fresh = json.loads((out / "fresh/results.json").read_text())
    validate_metadata(fresh)
    if fresh["axiom_audits"] != report["axiom_audits"]:
        raise ValueError("Replayed audit statements differ")
    if [(c["name"], c["accepted"]) for c in fresh["checks"]] != [(c["name"], c["accepted"]) for c in report["checks"]]:
        raise ValueError("Replayed checks differ")
    result = {"schema": 1, "status": "frozen-native-flashinfer-rmsnorm-first-block-replayed",
              "source_manifest_sha256": sha(packet / "source-manifest.json"),
              "packet_manifest_sha256": sha(packet / "manifest.json"), "source_files": len(hashes),
              "local_lean_modules": 30, "axiom_audits": 297, "source_instances": 6,
              "false_lean_claims_rejected": 11, "git_available_on_replay_path": False,
              "own_lean_compiled_cache_seeded": False,
              "first_block_scheduler_execution_proved": True,
              "first_block_partial_values_proved": True,
              "first_block_readonly_input_preservation_proved": True,
              "first_block_actual_trace_race_freedom_proved": True,
              "first_barrier_continuation_proved": True,
              "first_block_actual_trace_classification_proved": True,
              "second_reduction_execution_proved": False, "normalized_output_proved": False,
              "whole_kernel_execution_proved": False,
              "actual_trace_classification_proved": False, "source_reference_equality_proved": False,
              "source_certificates": 0, "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "replayer_sha256": sha(Path(__file__))}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": 30, "audits": 297,
                      "source_instances": 6, "rejections": 11, "git_on_path": False}))


if __name__ == "__main__":
    main()
