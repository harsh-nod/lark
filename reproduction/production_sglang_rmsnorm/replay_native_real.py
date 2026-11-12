"""Freshly rebuild the frozen real SGLang RMSNorm archive using pinned Mathlib.

Dependency sources are checked before restricting subprocess PATH to the Lean
toolchain. No own compiled objects are copied; Git is unavailable during replay.
"""

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
import time

MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
SOURCE_CONTROLS = (
    "source-unguarded-partial-store", "source-missing-first-barrier", "source-missing-second-barrier",
    "source-wrong-first-xor", "source-wrong-second-xor", "source-wrong-input-cache-address",
    "source-wrong-weight-cache-address", "source-reordered-pair-add", "source-aliased-output-cache",
    "source-wrong-output-address", "source-wrong-epsilon", "source-wrong-logical-width",
)
DIRECT_CONTROLS = (
    "wrong-source-block-fuel", "wrong-private-half-layout", "wrong-guarded-halt-pc",
    "wrong-square-reference", "wrong-output-length", "wrong-first-barrier-pc",
)
CONTROLS = SOURCE_CONTROLS + DIRECT_CONTROLS
REFERENCE_CONTROLS = ("reference-wrong-axis", "reference-wrong-epsilon", "reference-missing-weight", "reference-double-output")
TAMPER_CONTROLS = (
    "rehashed-main", "rehashed-model", "rehashed-reference", "rehashed-source", "rehashed-translation",
    "rehashed-configuration", "invented-ieee-proof", "invented-error-bound", "invented-paper-completion",
    "missing-whole-launch", "missing-reference-proof", "boolean-row-count", "wrong-output-count",
    "wrong-private-cache-count", "wrong-private-cell-count", "boolean-schema", "invented-unguarded-proof",
    "unknown-report-field",
)
SOURCE_SHA = "1758b5db41b411172c39b9d812121f1a4ba2f254f3643ccd55e89f8aac579257"



def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_metadata(report):
    required = {
        "schema": 1, "status": "native-sglang-canonical-real-whole-launch-checked",
        "model_profile": "native-sglang-rmsnorm-real-v23", "rows": {"min": 1, "max": 131072},
        "export_rows": [1, 3, 64, 131072], "block": 1024, "physical_warp": 64, "logical_warp": 32,
        "source_sha256": SOURCE_SHA, "local_lean_modules": 88, "local_real_modules": 4,
        "mathlib_revision": MATHLIB, "source_certificates": 4, "parameterized_source_certificate": True,
        "whole_kernel_execution_proved": True, "actual_trace_race_freedom_proved": True,
        "source_reference_equality_proved": True, "ieee_equivalence_proved": False,
        "floating_point_error_bound_proved": False, "original_paper_fully_reproduced": False,
        "model_calls": 0, "gpu_trials": 0, "false_lean_claims_rejected": 18, "false_claims_rejected": 40,
    }
    extra = {"checked_at_utc", "source_archive_sha256", "source_manifest_sha256", "library_axiom_audits",
             "main_axiom_audits", "export_axiom_audits", "checks"}
    message = "Unsupported SGLang RMSNorm real stage/scope metadata"
    require(type(report) is dict and set(report) == set(required) | extra, message)
    def same_typed(actual, expected):
        if type(actual) is not type(expected):
            return False
        if isinstance(expected, dict):
            return set(actual) == set(expected) and all(same_typed(actual[k], v) for k,v in expected.items())
        if isinstance(expected, list):
            return len(actual) == len(expected) and all(same_typed(a,b) for a,b in zip(actual,expected))
        return actual == expected
    require(all(same_typed(report[k], v) for k,v in required.items()), message)
    require(type(report["checked_at_utc"]) is str and bool(report["checked_at_utc"]), message)
    require(all(type(report[k]) is str and re.fullmatch(r"[0-9a-f]{64}", report[k])
                for k in ("source_archive_sha256", "source_manifest_sha256")), message)
    library, main, exports = (report[k] for k in ("library_axiom_audits", "main_axiom_audits", "export_axiom_audits"))
    require(type(library) is dict and len(library) == 750 and type(main) is dict and len(main) == 8
            and type(exports) is dict and set(exports) == {"1", "3", "64", "131072"}
            and all(type(v) is dict and v == main for v in exports.values()), message)
    for name, ax in {**library, **main}.items():
        require(type(name) is str and type(ax) is str and set(a.strip() for a in ax.split(",") if a.strip())
                <= {"propext", "Classical.choice", "Quot.sound"}, message)
    require({"LarkReal.NativeSglangRmsNorm.correct", "LarkNativeSglangRmsNorm.final_exec",
             "LarkNativeSglangRmsNorm.correct"} <= set(library), message)
    require(set(main) == {"LarkCertificate."+n for n in (
        "reference_data", "program_data", "segmentation_data", "segmentation", "race_free",
        "segment_equivalence", "kernel_eq_spec", "kernel_eq_spec_pre")}, message)
    names = [name for rows in (1, 3, 64, 131072) for name in (f"rows-{rows}", f"recheck-rows-{rows}")]
    names += list(CONTROLS + REFERENCE_CONTROLS + TAMPER_CONTROLS)
    checks = report["checks"]
    require(type(checks) is list and len(checks) == len(names), message)
    for i, (check, name) in enumerate(zip(checks, names)):
        require(type(check) is dict and set(check) == {"name", "accepted", "expected_accepted", "seconds", "timed_out"}
                and check["name"] == name and check["accepted"] is (i < 8)
                and check["expected_accepted"] is (i < 8) and check["timed_out"] is False
                and type(check["seconds"]) in (int, float) and math.isfinite(check["seconds"])
                and check["seconds"] >= 0, message)


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
    manifest = json.loads((packet / "manifest.json").read_text())
    require({"results.json", "source-manifest.json", "source.tar.gz"} <= set(manifest), "Incomplete packet manifest")
    for name, digest in manifest.items():
        require(Path(name).name == name and not (packet / name).is_symlink()
                and sha(packet / name) == digest, "Packet hash/path: " + name)
    report = json.loads((packet / "results.json").read_text())
    validate_metadata(report)
    require(sha(packet / "source.tar.gz") == report["source_archive_sha256"], "Archive hash differs")
    require(sha(packet / "source-manifest.json") == report["source_manifest_sha256"], "Source manifest hash differs")
    source_manifest = json.loads((packet / "source-manifest.json").read_text())
    out.mkdir(parents=True, exist_ok=False)
    project = out / "project"
    project.mkdir()
    seen, total = set(), 0
    with tarfile.open(packet / "source.tar.gz") as archive:
        for entry in archive:
            rel = PurePosixPath(entry.name)
            require(entry.isfile() and not rel.is_absolute() and ".." not in rel.parts and str(rel) == entry.name
                    and not entry.name.endswith((".olean", ".ilean")) and ".git" not in rel.parts and ".lake" not in rel.parts
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
    for rows in (3, 64, 131072):
        row_log = run(f"rows-{rows}", lake + ["env", "lean", f"rows-{rows}.lean"], True)
        row_audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", row_log))
        require(row_audits == report["main_axiom_audits"], "Source instance audit differs")
    for name in CONTROLS:
        run(name, lake + ["env", "lean", name + ".lean"], False)
    result = {
        "schema": 1, "status": "frozen-sglang-canonical-real-whole-launch-archive-replayed",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "source_manifest_sha256": sha(packet / "source-manifest.json"),
        "fresh_source_files": len(seen), "local_lean_modules": report["local_lean_modules"],
        "axiom_audits": len(all_audits) + 3 * len(report["main_axiom_audits"]),
        "unique_axiom_declarations": len(all_audits), "source_instances": 4, "dependency_sources_checked_before_path_restriction": dependency_records,
        "git_available_on_replay_path": False, "own_lean_compiled_cache_seeded": False,
        "external_pinned_mathlib_cache_seeded": True, "frozen_python_reader_replayed": True,
        "dependency_path_overrides_used": True, "original_git_lock_unchanged": True,
        "source_certificates": 4, "parameterized_source_certificate": True,
        "whole_kernel_execution_proved": True, "actual_trace_race_freedom_proved": True,
        "source_reference_equality_proved": True,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "gpu_trials": 0, "model_calls": 0,
        "false_lean_claims_rejected": len(CONTROLS), "checks": checks,
    }
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "source_certificates", "axiom_audits", "false_lean_claims_rejected")}))


if __name__ == "__main__":
    main()
