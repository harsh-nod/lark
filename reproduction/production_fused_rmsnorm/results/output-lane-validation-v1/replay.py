"""Rebuild a frozen scalar-prefix source archive, without Git or own Lean cache."""

import argparse
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True,
                        help="Lean 4.19.0 toolchain bin directory; sole subprocess PATH")
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Output must be outside Git")
    require((lean_bin / "lean").is_file() and (lean_bin / "lake").is_file(), "Lean/lake binaries missing")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable on replay PATH")
    for name, digest in json.loads((packet / "manifest.json").read_text()).items():
        require(Path(name).name == name and sha(packet / name) == digest, "Packet hash/path: " + name)
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    report = json.loads((packet / "results.json").read_text())
    require(report["status"] in {"native-inout-scalar-prefix-checked", "native-inout-first-wave-checked",
                                 "native-inout-first-block-checked", "native-inout-second-block-checked", "native-inout-output-lane-checked"}, "Wrong packet stage")
    require(report["source_certificates"] == 0 and not report["whole_kernel_execution_proved"]
            and not report["actual_trace_classification_proved"]
            and not report["canonical_source_equivalence_proved"]
            and not report["original_paper_fully_reproduced"], "Invented whole-source/paper claim")
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
            require(entry.size <= 8_000_000 and total <= 50_000_000, "Source archive too large")
            blob = archive.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == source_manifest[entry.name], "Source hash: " + entry.name)
            path = project / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists(), "Source closure/cache mismatch")
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("PYTHONPATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    checks = []
    for record in report["checks"]:
        name, expected = record["name"], record["expected_accepted"]
        require(re.fullmatch(r"[a-z0-9-]+", name), "Unexpected check name")
        if name == "frozen-reader-replay":
            command = [sys.executable, "validate_source.py"]
        elif name == "fresh-build":
            command = ["lake", "build"]
        elif name == "positive-cast-and-preservation-witnesses":
            command = ["lake", "env", "lean", "Witnesses.lean"]
        else:
            command = ["lake", "env", "lean", name + ".lean"]
        start = time.monotonic()
        run = subprocess.run(command, cwd=project, env=env, text=True, capture_output=True,
                             timeout=600 if report["status"] in {"native-inout-first-block-checked", "native-inout-second-block-checked", "native-inout-output-lane-checked"}
                             and name == "fresh-build" else 300)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "sorryAx" not in log and "error:" not in log
        require(accepted == expected, name + ": unexpected acceptance\n" + log)
        if not expected:
            require("is false" in log and "error:" in log, name + ": wrong rejection gate\n" + log)
        if name == "fresh-build":
            audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
            require(audits == report["axiom_audits"], "Axiom audit mismatch")
            for ax in audits.values():
                require(not (set(x.strip() for x in ax.split(",") if x.strip())
                             - {"propext", "Classical.choice", "Quot.sound"}), "Unexpected axiom")
        checks.append({"name": name, "expected_accepted": expected, "exit_code": run.returncode,
                       "seconds": time.monotonic() - start, "timed_out": False})
    result = {
        "schema": 1, "status": ("frozen-output-lane-archive-replayed" if report["status"] == "native-inout-output-lane-checked"
                                  else "frozen-second-block-archive-replayed" if report["status"] == "native-inout-second-block-checked"
                                  else "frozen-first-block-archive-replayed" if report["status"] == "native-inout-first-block-checked"
                                  else "frozen-first-wave-archive-replayed" if report["status"] == "native-inout-first-wave-checked"
                                  else "frozen-scalar-prefix-archive-replayed"), "fresh_source_files": len(seen),
        "local_lean_modules": report["local_lean_modules"], "axiom_audits": len(report["axiom_audits"]),
        "false_claims_rejected": sum(not c["expected_accepted"] for c in checks), "checks": checks,
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "git_available_on_path": False, "frozen_python_reader_replayed": True, "own_lean_compiled_cache_seeded": False,
        "source_certificates": 0, "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
        "canonical_source_equivalence_proved": False, "gpu_trials": 0, "model_calls": 0,
        "original_paper_fully_reproduced": False,
    }
    for key, value in report.items():
        if key.startswith(("scalar_prefix_", "first_native_wave_", "first_native_block_", "second_native_block_", "output_lane_")):
            result[key] = value
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "local_lean_modules", "axiom_audits", "false_claims_rejected")}), flush=True)


if __name__ == "__main__":
    main()
