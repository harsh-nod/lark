"""Replay frozen SGLang RMSNorm native wave entry and first XOR snapshot without Git or owned caches."""

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
        "schema": 1, "status": "native-sglang-rmsnorm-wave-entry-and-first-snapshot-checked",
        "local_lean_modules": 33, "library_axiom_audits": 260, "source_instances": 6,
        "source_axiom_audits_per_instance": 16, "false_lean_claims_rejected": 11,
        "full_source_binding_proved": True, "native_wave_entry_success_proved": True,
        "native_warp_scheduler_prefix_transition_proved": True, "first_shuffle_executed_proved": True,
        "wave_threads": 64, "logical_partition_width": 32, "scalar_prefix_instructions_per_lane": 330,
        "snapshot_exit_pc": 45, "source_lane_fuel": 512, "source_warp_fuel": 8,
        "input_cache_cells_per_thread": 16, "weight_cache_cells_per_thread": 16, "new_access_events_per_wave": 5120,
        "private_cache_values_and_other_thread_state_framed": True,
        "arbitrary_prior_trace_preserved": True, "prior_trace_safety_assumed": False,
        "new_wave_trace_classified": True, "initial_wave_snapshot_race_freedom_proved": True,
        "all_five_first_reduction_shuffles_proved": False, "original_partial_store_reachability_proved": False,
        "first_block_barrier_reached_proved": False, "whole_kernel_execution_proved": False,
        "actual_whole_trace_classification_proved": False, "source_reference_equality_proved": False,
        "source_certificates": 0, "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
    }
    extra = {"axiom_audits", "checks", "source_archive_sha256", "source_manifest_sha256"}
    if (set(report) != set(required) | extra
            or any(type(report.get(k)) is not type(v) or report[k] != v for k, v in required.items())):
        raise ValueError("Unsupported SGLang RMSNorm wave-entry stage/scope metadata")
    audits = report["axiom_audits"]
    names = ["fresh-build"] + [variant + "_rows_" + str(rows)
                               for variant in ("native_original", "native_fixed")
                               for rows in (1, 3, 131072)]
    if set(audits) != set(names) or len(audits["fresh-build"]) != 260:
        raise ValueError("Wave-entry audit coverage differs")
    for name, values in audits.items():
        if (name != "fresh-build" and len(values) != 16
                or any(not set(v) <= {"propext", "Classical.choice", "Quot.sound"} for v in values.values())):
            raise ValueError("Wave-entry axiom closure differs")
    principals = {"LarkTraceTransport.run_lane_append", "LarkNativeSglangRmsNorm.carried_prefix_run",
                  "LarkNativeSglangRmsNorm.prefix_frame", "LarkNativeSglangRmsNorm.prefix_fold_run",
                  "LarkNativeSglangRmsNorm.wave_entry_success", "LarkNativeSglangRmsNorm.wave_first_snapshot_step",
                  "LarkNativeSglangRmsNorm.wave_snapshot_values", "LarkNativeSglangRmsNorm.wave_snapshot_trace_tail"}
    if not principals <= set(audits["fresh-build"]):
        raise ValueError("Missing native wave-entry principal")
    source_principals = {"source_binding", "source_carried_lane", "source_memory_frame", "source_fold_execution",
                         "source_wave_entry_success", "source_native_warp_transition", "source_snapshot_values",
                         "source_cached_halves", "source_readonly_globals", "source_snapshot_preserves", "source_past_trace",
                         "source_trace_length", "source_complete_partitions", "source_initial_snapshot_race_free",
                         "source_peer_stays_partition", "source_first_shuffle_site"}
    if any(set(v) != source_principals for n, v in audits.items() if n != "fresh-build"):
        raise ValueError("Source wave-entry principals differ")
    names += ["aliased-input-cache-slot", "wrong-input-cache-address", "aliased-weight-cache-slot",
              "wrong-weight-cache-address", "wrong-pair-grouping", "wrong-first-shuffle",
              "crossed-logical-partition", "invented-full-reduction-pc", "erased-prior-trace",
              "invented-block-barrier", "corrupted-other-thread-cache"]
    checks = report["checks"]
    if (len(checks) != len(names) or [c["name"] for c in checks] != names
            or any(c["accepted"] is not (i < 7) or type(c["exit_code"]) is not int
                   or c["exit_code"] != (0 if i < 7 else 1) for i, c in enumerate(checks))):
        raise ValueError("Wave-entry source/control coverage differs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    manifest = json.loads((packet / "manifest.json").read_text())
    if not {"results.json", "source-manifest.json", "source.tar.gz"} <= set(manifest):
        raise ValueError("Incomplete packet manifest")
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
    run = subprocess.run([sys.executable, str(source / "reproduction/production_sglang_rmsnorm/check_wave_entry.py"),
                          "--output", str(out / "fresh"), "--lean-bin", str(bin_dir)], cwd=source, env=env,
                         capture_output=True, text=True, timeout=900)
    (out / "replay.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError("Frozen component replay failed: " + run.stdout + run.stderr)
    fresh = json.loads((out / "fresh/results.json").read_text())
    validate_metadata(fresh)
    if fresh["axiom_audits"] != report["axiom_audits"]:
        raise ValueError("Replayed audit statements differ")
    if [(c["name"], c["accepted"]) for c in fresh["checks"]] != [(c["name"], c["accepted"]) for c in report["checks"]]:
        raise ValueError("Replayed checks differ")
    result = {"schema": 1, "status": "frozen-native-sglang-rmsnorm-wave-entry-replayed",
              "source_manifest_sha256": sha(packet / "source-manifest.json"),
              "packet_manifest_sha256": sha(packet / "manifest.json"), "source_files": len(hashes),
              "local_lean_modules": 33, "axiom_audits": 356, "source_instances": 6,
              "false_lean_claims_rejected": 11, "git_available_on_replay_path": False,
              "own_lean_compiled_cache_seeded": False, "whole_kernel_execution_proved": False,
              "original_partial_store_reachability_proved": False, "first_shuffle_executed_proved": True, "arbitrary_prior_trace_preserved": True, "new_wave_trace_classified": True,
              "actual_whole_trace_classification_proved": False, "source_reference_equality_proved": False,
              "source_certificates": 0, "model_calls": 0, "gpu_trials": 0,
              "original_paper_fully_reproduced": False, "replayer_sha256": sha(Path(__file__))}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": 33, "audits": 356,
                      "source_instances": 6, "rejections": 11, "git_on_path": False}))


if __name__ == "__main__":
    main()
