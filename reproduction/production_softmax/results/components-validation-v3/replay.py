"""Rebuild frozen softmax components and repeat the full finite address replay."""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_hash(path):
    result = hashlib.sha256()
    with gzip.open(path, "rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(part)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--finite-trace-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, finite, out, lean_bin = (p.resolve() for p in (args.packet, args.finite_trace_packet, args.output, args.lean_bin))
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Output must be outside Git")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable on replay PATH")
    version = subprocess.check_output([str(lean_bin / "lean"), "--version"], text=True, timeout=30)
    require("version 4.19.0" in version, "Pinned Lean4.19.0 required")
    for directory in (packet, finite):
        for name, digest in json.loads((directory / "manifest.json").read_text()).items():
            require(Path(name).name == name and sha(directory / name) == digest, "Packet path/hash: " + name)
    report = json.loads((packet / "results.json").read_text())
    require(report["status"] == "native-softmax-source-and-instruction-witness-checked", "Wrong proof stage")
    require(type(report.get("source_certificates")) is int and report["source_certificates"] == 0,
            "Invented source certificate")
    require(all(report.get(name) is False for name in (
        "whole_kernel_execution_proved", "intermediate_state_reachability_proved",
        "actual_trace_universal_classification_proved", "canonical_source_equivalence_proved",
        "ieee_equivalence_proved", "original_paper_fully_reproduced")), "Invented whole-source/reference claim")
    principal = {"source_program_data", "source_reader_trace", "source_writer_trace", "source_guard_trace",
                 "source_seed_code", "source_seed_evaluates", "LarkNativeSoftmax.seed_expr",
                 "LarkNativeSoftmax.zero_denominator_refused", "LarkNativeSoftmax.reader_step",
                 "LarkNativeSoftmax.writer_step", "LarkNativeSoftmax.pair_conflict"}
    require(principal <= report["axiom_audits"].keys(), "Principal instruction witness audits absent")
    require(report.get("seed_denominator") == 4294967296
            and report.get("named_seed_evaluation_proved") is True
            and report.get("zero_denominator_seed_rejected") is True,
            "Executable seed checks absent; earlier zero-denominator checkpoints are superseded")
    require(sha(packet / "source.tar.gz") == report["source_archive_sha256"], "Source archive differs")
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    seen, total = set(), 0
    with tarfile.open(packet / "source.tar.gz") as archive:
        for entry in archive:
            rel = PurePosixPath(entry.name)
            require(entry.isfile() and not rel.is_absolute() and ".." not in rel.parts
                    and ".git" not in rel.parts and ".lake" not in rel.parts
                    and entry.name not in seen and entry.name in source_manifest,
                    "Unexpected archived source: " + entry.name)
            total += entry.size
            require(entry.size < 8_000_000 and total < 50_000_000, "Archive too large")
            data = archive.extractfile(entry).read()
            require(hashlib.sha256(data).hexdigest() == source_manifest[entry.name], "Source hash differs")
            path = project / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            seen.add(entry.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists()
            and not any(project.rglob("*.olean")), "Own source/cache mismatch")
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    checks = []
    for record in report["checks"]:
        name, expected = record["name"], record["expected_accepted"]
        require(re.fullmatch(r"[a-z0-9-]+", name), "Unexpected check name")
        command = ([sys.executable, "validate_source.py"] if name == "frozen-reader"
                   else ["lake", "build"] if name == "fresh-build"
                   else ["lake", "env", "lean", name + ".lean"])
        before = time.monotonic()
        result = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        accepted = result.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("is false" in log and "error:" in log and "maximum" not in log, "Wrong rejection gate")
        if name == "fresh-build":
            audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
            require(audits == report["axiom_audits"], "Fresh axiom audits differ")
            for ax in audits.values():
                require(set(a.strip() for a in ax.split(",") if a.strip()) <=
                        {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom")
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": result.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    before = time.monotonic()
    run = subprocess.run([sys.executable, "reproduction/production_softmax/trace_full.py",
                          "--output", str(out / "finite-replay")], cwd=project, env=env,
                         capture_output=True, text=True, timeout=180)
    (out / "finite-replay.log").write_text(run.stdout + run.stderr)
    require(run.returncode == 0, "Frozen finite replay failed")
    comparisons = []
    for name in ("native_race", "native_fixed"):
        original = json.loads((finite / (name + ".json")).read_text())
        replay = json.loads((out / "finite-replay" / (name + ".json")).read_text())
        for key in ("case", "instructions", "accesses", "counts", "footprint_classification_failures",
                    "all_threads_halted", "final_block_epoch", "missing_output_cells", "first_conflict",
                    "canonical_witness", "source_sha256"):
            require(original[key] == replay[key], "Finite trace record differs: " + name + ":" + key)
        content_hash = trace_hash(finite / original["trace_file"])
        require(trace_hash(out / "finite-replay" / replay["trace_file"]) == content_hash, "Complete address trace differs")
        comparisons.append({"case": name, "accesses": replay["accesses"], "trace_content_sha256": content_hash})
    checks.append({"name": "full-finite-source-replay", "accepted": True, "expected_accepted": True,
                   "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    result = {
        "schema": 1, "status": "frozen-softmax-components-and-complete-finite-traces-replayed",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "fresh_source_files": len(seen), "local_lean_modules": report["local_lean_modules"],
        "axiom_audits": len(report["axiom_audits"]), "false_lean_claims_rejected": report["false_lean_claims_rejected"],
        "git_available_on_path": False, "own_lean_compiled_cache_seeded": False,
        "checks": checks, "complete_finite_traces_compared": comparisons,
        "source_certificates": 0, "instruction_trace_counterexample_proved": True,
        "named_seed_evaluation_proved": True, "zero_denominator_seed_rejected": True,
        "whole_kernel_execution_proved": False, "intermediate_state_reachability_proved": False,
        "actual_trace_universal_classification_proved": False, "canonical_source_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": result["local_lean_modules"],
                      "audits": result["axiom_audits"], "rejections": result["false_lean_claims_rejected"]}))


if __name__ == "__main__":
    main()
