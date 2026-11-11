"""Replay the source-bound maximum-prefix archive without Git or own Lean cache."""

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


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_sha(path):
    digest = hashlib.sha256()
    with gzip.open(path, "rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(part)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--finite-trace-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    packet, finite, out, lean_bin = (p.resolve() for p in (args.packet, args.finite_trace_packet, args.output, args.lean_bin))
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable on replay PATH")
    version = subprocess.check_output([str(lean_bin / "lean"), "--version"], text=True, timeout=30)
    require("version 4.19.0" in version, "Pinned Lean4.19.0 required")
    for folder in (packet, finite):
        for name, digest in json.loads((folder / "manifest.json").read_text()).items():
            require(Path(name).name == name and sha(folder / name) == digest, "Packet path/hash differs: " + name)
    report = json.loads((packet / "results.json").read_text())
    require(report.get("status") == "native-softmax-source-bound-maximum-prefix-checked"
            and report.get("stage") == "max-prefix", "Wrong proof stage")
    require(type(report.get("source_certificates")) is int and report["source_certificates"] == 0,
            "Invented source certificate")
    require(all(report.get(name) is False for name in (
        "whole_kernel_execution_proved", "conflict_witness_state_reachability_proved",
        "actual_trace_universal_classification_proved", "canonical_source_equivalence_proved",
        "ieee_equivalence_proved", "original_paper_fully_reproduced", "race_freedom_assumed")),
        "Invented whole-source/reference claim or assumed race freedom")
    require(all(report.get(name) is True for name in (
        "actual_maximum_prefix_execution_proved", "starts_at_actual_initializer",
        "all_prefix_accesses_are_input_reads_proved", "source_ordered_maximum_value_proved",
        "all_memory_and_epochs_preserved_proved", "prefix_race_freedom_proved")), "Missing prefix claims")
    require(report.get("endpoint_pc") == 20 and report.get("accesses_per_lane") == 56
            and report.get("original_lane_fuel") == 4096, "Wrong prefix endpoint/accesses/fuel")
    principal = {"source_program_data", "source_prefix_initial_run", "source_prefix_initial_value",
                 "source_prefix_initial_inputs", "source_prefix_initial_rf", "source_prefix_initial_frames",
                 "source_prefix_cost", "source_prefix_word_0", "source_prefix_word_81",
                 "LarkNativeSoftmax.initial_max_prefix_run", "LarkNativeSoftmax.initial_max_prefix_inputs",
                 "LarkNativeSoftmax.max_prefix_cost_exact", "LarkNativeSoftmax.seed_expr"}
    require(principal <= report["axiom_audits"].keys(), "Principal maximum-prefix audits absent")
    require(sha(packet / "source.tar.gz") == report["source_archive_sha256"], "Source archive differs")
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    seen, total = set(), 0
    with tarfile.open(packet / "source.tar.gz") as archive:
        for member in archive:
            rel = PurePosixPath(member.name)
            require(member.isfile() and not rel.is_absolute() and ".." not in rel.parts
                    and ".git" not in rel.parts and ".lake" not in rel.parts
                    and member.name not in seen and member.name in source_manifest, "Unsafe/unexpected source entry")
            total += member.size
            require(member.size < 8_000_000 and total < 50_000_000, "Source archive exceeds bounds")
            content = archive.extractfile(member).read()
            require(hashlib.sha256(content).hexdigest() == source_manifest[member.name], "Source hash differs")
            target = project / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
            seen.add(member.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists()
            and not any(project.rglob("*.olean")), "Unexpected own source/cache")
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
        run = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("is false" in log and "maximum recursion depth" not in log
                    and "maximum heartbeats" not in log, "Wrong rejection gate: " + name)
        if name == "fresh-build":
            audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
            require(audits == report["axiom_audits"], "Fresh axiom audits differ")
            for axioms in audits.values():
                require(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                        {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom")
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    before = time.monotonic()
    run = subprocess.run([sys.executable, "reproduction/production_softmax/trace_full.py", "--output", str(out / "finite-replay")],
                         cwd=project, env=env, capture_output=True, text=True, timeout=180)
    (out / "finite-replay.log").write_text(run.stdout + run.stderr)
    require(run.returncode == 0, "Frozen full finite source replay failed")
    comparisons = []
    for case in ("native_race", "native_fixed"):
        old = json.loads((finite / (case + ".json")).read_text())
        new = json.loads((out / "finite-replay" / (case + ".json")).read_text())
        for key in ("case", "instructions", "accesses", "counts", "footprint_classification_failures",
                    "all_threads_halted", "final_block_epoch", "missing_output_cells", "first_conflict",
                    "canonical_witness", "source_sha256"):
            require(old[key] == new[key], "Finite trace record differs: " + case + ":" + key)
        digest = trace_sha(finite / old["trace_file"])
        require(trace_sha(out / "finite-replay" / new["trace_file"]) == digest, "Complete finite trace differs")
        comparisons.append({"case": case, "accesses": new["accesses"], "trace_content_sha256": digest})
    checks.append({"name": "full-finite-source-replay", "accepted": True, "expected_accepted": True,
                   "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    result = {
        "schema": 1, "status": "frozen-softmax-maximum-prefix-and-finite-traces-replayed", "stage": "max-prefix",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "local_lean_modules": report["local_lean_modules"], "axiom_audits": len(report["axiom_audits"]),
        "false_lean_claims_rejected": report["false_lean_claims_rejected"], "checks": checks,
        "git_available_on_path": False, "own_lean_compiled_cache_seeded": False,
        "complete_finite_traces_compared": comparisons, "actual_maximum_prefix_execution_proved": True,
        "starts_at_actual_initializer": True, "endpoint_pc": 20, "accesses_per_lane": 56,
        "prefix_race_freedom_proved": True, "source_certificates": 0, "whole_kernel_execution_proved": False,
        "conflict_witness_state_reachability_proved": False, "actual_trace_universal_classification_proved": False,
        "canonical_source_equivalence_proved": False, "ieee_equivalence_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "gpu_trials": 0,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": result["local_lean_modules"],
                      "audits": result["axiom_audits"], "rejections": result["false_lean_claims_rejected"]}))


if __name__ == "__main__":
    main()
