"""Rebuild complete frozen RoPE certificates without Git or an owned proof cache."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_names():
    positives = []
    for layout in ("interleaved", "split-half"):
        for rows in (1, 3, 256, 65535):
            name = f"{layout}-{rows}"
            positives += [(name, True), ("recheck-" + name, True)]
    negatives = [
        "wrong-loop-stride", "wrong-cache-half", "missing-key-store", "wrong-pair-arithmetic",
        "invented-none-launch", "invented-final-race", "missing-key-extraction", "wrong-first-query-value",
        "rehashed-main", "rehashed-model", "rehashed-reference", "invented-ieee-proof",
        "invented-paper-completion", "missing-inout-proof", "boolean-row-count", "unknown-proof-claim",
    ]
    return positives + [(name, False) for name in negatives]


def validate_metadata(report):
    required = {
        "schema": 1, "status": "native-rope-source-bound-whole-launch-checked",
        "model_profile": "native-rope-whole-v19", "local_lean_modules": 25,
        "source_instances": 8, "source_certificates": 8, "main_axiom_audits_per_instance": 10,
        "false_lean_claims_rejected": 8, "rehashed_false_claims_rejected": 8,
        "both_layouts_proved": True, "whole_kernel_execution_proved": True,
        "actual_trace_race_freedom_proved": True, "seeded_inout_proved": True,
        "both_output_buffers_extracted": True, "source_reference_equality_proved": True,
        "scalar_interpretation": "arbitrary scalar operations and explicit half conversions",
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    extra = {"library_axiom_audits", "checks", "source_archive_sha256", "source_manifest_sha256"}
    if (type(report) is not dict or set(report) != set(required) | extra
            or any(type(report.get(k)) is not type(v) or report[k] != v for k, v in required.items())):
        raise ValueError("Unsupported native RoPE whole-launch stage/scope metadata")
    audits = report["library_axiom_audits"]
    principals = {"LarkInOutScalar.correct_from_pre", "LarkNativeRope.final_launch",
                  "LarkNativeRope.final_race_free", "LarkNativeRope.final_extract", "LarkNativeRope.correct"}
    if (type(audits) is not dict or len(audits) != 157 or not principals <= set(audits)
            or any(type(v) is not str or not {a.strip() for a in v.split(",") if a.strip()}
                   <= {"propext", "Classical.choice", "Quot.sound"} for v in audits.values())):
        raise ValueError("Unsupported native RoPE whole-launch principal audits")
    checks = report["checks"]
    if type(checks) is not list or len(checks) != 32:
        raise ValueError("Unsupported native RoPE whole-launch check coverage")
    for check, (name, accepted) in zip(checks, check_names()):
        if (type(check) is not dict
                or set(check) != {"name", "accepted", "expected_accepted", "seconds", "timed_out"}
                or check["name"] != name or check["accepted"] is not accepted
                or check["expected_accepted"] is not accepted or check["timed_out"] is not False
                or type(check["seconds"]) not in (int, float)
                or not math.isfinite(check["seconds"]) or check["seconds"] < 0):
            raise ValueError("Unsupported native RoPE whole-launch check coverage")
    if any(type(report[k]) is not str or re.fullmatch(r"[0-9a-f]{64}", report[k]) is None
           for k in ("source_archive_sha256", "source_manifest_sha256")):
        raise ValueError("Unsupported native RoPE whole-launch source binding")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    if any((p / ".git").exists() for p in (out, *out.parents)):
        raise ValueError("Choose replay output outside Git")
    manifest = json.loads((packet / "manifest.json").read_text())
    if not {"results.json", "source.tar.gz", "source-manifest.json"} <= set(manifest):
        raise ValueError("Incomplete packet manifest")
    for name, expected in manifest.items():
        path = packet / name
        if Path(name).name != name or path.is_symlink() or sha(path) != expected:
            raise ValueError("Packet binding differs: " + name)
    report = json.loads((packet / "results.json").read_text())
    validate_metadata(report)
    if (sha(packet / "source.tar.gz") != report["source_archive_sha256"]
            or sha(packet / "source-manifest.json") != report["source_manifest_sha256"]):
        raise ValueError("Source binding differs")
    # All stage/scope checks above run before making output or extracting source.
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
                    or entry.name not in hashes or ".lake" in path.parts
                    or entry.name.endswith((".olean", ".ilean"))):
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
    env["LARK_NATIVE_ROPE_CACHE"] = str(out / "fresh-proof-cache")
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    if shutil.which("git", path=env["PATH"]) is not None or (out / "fresh-proof-cache").exists():
        raise ValueError("Git or an owned proof cache unexpectedly available")
    version = subprocess.check_output([str(bin_dir / "lean"), "--version"], env=env, text=True, timeout=30)
    if "version 4.19.0" not in version:
        raise ValueError("Pinned Lean4.19.0 required")
    run = subprocess.run([sys.executable, str(source / "reproduction/production_rope/run_whole.py"),
                          "--output", str(out / "fresh"), "--lean", str(bin_dir / "lean")],
                         cwd=source, env=env, capture_output=True, text=True, timeout=900)
    (out / "replay.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError("Frozen whole-launch replay failed: " + run.stdout + run.stderr)
    fresh = json.loads((out / "fresh/results.json").read_text())
    validate_metadata(fresh)
    if fresh["library_axiom_audits"] != report["library_axiom_audits"]:
        raise ValueError("Replayed audit statements differ")
    if [(c["name"], c["accepted"]) for c in fresh["checks"]] != [(c["name"], c["accepted"]) for c in report["checks"]]:
        raise ValueError("Replayed checks differ")
    for name, _ in check_names()[::2][:8]:
        first = json.loads((packet / name / "report.json").read_text())
        second = json.loads((out / "fresh" / name / "report.json").read_text())
        if first != second:
            raise ValueError("Replayed source certificate differs: " + name)
        for filename in second["files"]:
            path = packet / name / filename
            if path.is_symlink() or path.read_bytes() != (out / "fresh" / name / filename).read_bytes():
                raise ValueError("Frozen certificate bytes differ: " + name + "/" + filename)
    result = {"schema": 1, "status": "frozen-native-rope-whole-launch-replayed",
              "source_manifest_sha256": sha(packet / "source-manifest.json"),
              "packet_manifest_sha256": sha(packet / "manifest.json"), "source_files": len(hashes),
              "local_lean_modules": 25, "library_axiom_audits": 157, "main_axiom_audits": 80,
              "source_certificates": 8, "source_rechecks": 8, "false_lean_claims_rejected": 8,
              "rehashed_false_claims_rejected": 8, "git_available_on_replay_path": False,
              "own_lean_compiled_cache_seeded": False, "whole_kernel_execution_proved": True,
              "actual_trace_race_freedom_proved": True, "source_reference_equality_proved": True,
              "model_calls": 0, "gpu_trials": 0, "original_paper_fully_reproduced": False,
              "replayer_sha256": sha(Path(__file__))}
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "certificates": 8, "audits": 237, "git_on_path": False}))


if __name__ == "__main__":
    main()
