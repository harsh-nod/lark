"""Freshly rebuild the frozen real interleaved Q/K normalization/rotary archive using pinned Mathlib.

Dependency sources are checked before restricting subprocess PATH to the Lean
toolchain. No own compiled objects are copied; Git is unavailable during replay.
"""

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

MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
CONTROLS = (
    "source-wrong-xor", "source-widened-shuffle", "source-wrong-weight", "source-wrong-mean",
    "source-wrong-cache", "source-wrong-rotation", "source-aliased-last-store", "missing-last-output",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--dependency-project", type=Path, required=True,
                        help="Initialized lean-real project supplying only pinned external packages")
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Output must be outside Git")
    require(all((lean_bin / name).is_file() for name in ("lean", "lake")), "Lean/lake missing")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable on replay PATH")
    for name, digest in json.loads((packet / "manifest.json").read_text()).items():
        require(Path(name).name == name and sha(packet / name) == digest, "Packet hash/path: " + name)
    report = json.loads((packet / "results.json").read_text())
    require(report["status"] == "native-qknorm-rope-interleaved-canonical-real-whole-launch-checked"
            and report["model_profile"] == "native-qknorm-rope-interleaved-real-v20"
            and report["mathlib_revision"] == MATHLIB and report["export_rows"] == [1, 3, 256, 65535]
            and type(report["source_certificates"]) is int and report["source_certificates"] == 4,
            "Wrong profile/stage/specializations")
    require(all(report.get(name) is True for name in (
        "parameterized_library_proof", "whole_kernel_execution_proved", "actual_trace_race_freedom_proved",
        "readonly_inputs_proved", "all_output_elements_extracted", "source_reference_equality_proved")),
        "Missing whole-launch reference claim")
    require(all(report.get(name) is False for name in (
        "split_half_proved", "ieee_equivalence_proved", "floating_point_error_bound_proved", "original_paper_fully_reproduced")),
        "Invented IEEE/paper claim")
    require("LarkReal.NativeQKNormRope.correct" in report["library_axiom_audits"]
            and "LarkCertificate.kernel_eq_spec_pre" in report["main_axiom_audits"], "Principal audits absent")
    require(sha(packet / "source.tar.gz") == report["source_archive_sha256"], "Archive hash differs")
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
            require(entry.size <= 8_000_000 and total <= 50_000_000, "Source archive too large")
            blob = archive.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == source_manifest[entry.name], "Source hash: " + entry.name)
            path = project / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists(), "Source/cache mismatch")
    require(not any(project.rglob("*.olean")), "Compiled own objects present before build")
    lock = json.loads((project / "lake-manifest.json").read_text())
    packages = lock["packages"]
    require(len(packages) == 9 and all(p["type"] == "git" for p in packages)
            and [p["rev"] for p in packages if p["name"] == "mathlib"] == [MATHLIB], "Wrong dependency lock")
    seeds, dependency_records = {}, []
    for package in packages:
        name = package["name"]
        require(re.fullmatch(r"[A-Za-z0-9_]+", name), "Unexpected dependency name")
        path = (args.dependency_project / ".lake/packages" / name).resolve()
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=path, capture_output=True, text=True, timeout=30)
        clean = subprocess.run(["git", "diff", "--quiet", "--no-ext-diff", "--no-textconv", "HEAD", "--"],
                               cwd=path, capture_output=True, timeout=30)
        require(head.returncode == 0 and head.stdout.strip() == package["rev"] and clean.returncode == 0,
                "Dependency source differs: " + name)
        seeds[name] = path
        dependency_records.append({"name": name, "revision": package["rev"], "clean": True})
    # Path overrides prevent Lake from invoking Git or trying to refresh an
    # external dependency. The original Git lock remains unchanged in the archive.
    overrides = [dict(package, type="path", dir=str(seeds[package["name"]])) for package in packages]
    overrides_path = out / "dependency-path-overrides.json"
    overrides_path.write_text(json.dumps({"version": lock["version"], "packages": overrides}, indent=2) + "\n")
    lake = ["lake", "--packages=" + str(overrides_path)]
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    checks = []

    def run(name, command, expected, timeout=300):
        before = time.monotonic()
        result = subprocess.run(command, cwd=project, env=env, text=True, capture_output=True, timeout=timeout)
        log = result.stdout + result.stderr
        (out / (name + ".log")).write_text(log)
        accepted = result.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected, "Unexpected acceptance: " + name + "\n" + log)
        if not expected:
            require("error:" in log and ("is false" in log or "⊢ False" in log)
                    and "maximum recursion" not in log and "Stack overflow" not in log
                    and "maximum number of heartbeats" not in log, "Wrong rejection gate: " + name)
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected,
                       "exit_code": result.returncode, "seconds": time.monotonic() - before, "timed_out": False})
        return log

    run("frozen-reader-replay", [sys.executable, "validate_source.py"], True)
    build_log = run("fresh-build", lake + ["build"], True, 600)
    all_audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", build_log))
    require(all_audits == {**report["library_axiom_audits"], **report["main_axiom_audits"]}, "Fresh axiom audits differ")
    for name, ax in all_audits.items():
        require(set(a.strip() for a in ax.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"}, "Extra axiom: " + name)
    for rows in (3, 256, 65535):
        run(f"rows-{rows}", lake + ["env", "lean", f"rows-{rows}.lean"], True)
    for name in CONTROLS:
        run(name, lake + ["env", "lean", name + ".lean"], False)
    result = {
        "schema": 1, "status": "frozen-qknorm-rope-interleaved-canonical-real-whole-launch-archive-replayed",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "fresh_source_files": len(seen), "local_lean_modules": report["local_lean_modules"],
        "axiom_audits": len(all_audits), "dependency_sources_checked_before_path_restriction": dependency_records,
        "git_available_on_replay_path": False, "own_lean_compiled_cache_seeded": False,
        "external_pinned_mathlib_cache_seeded": True, "frozen_python_reader_replayed": True,
        "dependency_path_overrides_used": True, "original_git_lock_unchanged": True,
        "source_certificates": 4, "parameterized_library_proof": True,
        "whole_kernel_execution_proved": True, "actual_trace_race_freedom_proved": True,
        "readonly_inputs_proved": True, "all_output_elements_extracted": True, "source_reference_equality_proved": True,
        "split_half_proved": False, "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "gpu_trials": 0, "model_calls": 0,
        "false_lean_claims_rejected": len(CONTROLS), "checks": checks,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "source_certificates", "axiom_audits", "false_lean_claims_rejected")}))


if __name__ == "__main__":
    main()
