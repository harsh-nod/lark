"""Replay the frozen softmax real reference proof without Git or own caches."""

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
CONTROLS = {
    "grid-fixed-load-guard", "grid-fixed-division", "grid-fixed-stride",
    "uniform-dropped-column", "uniform-missing-division", "nonpositive-source-denominator",
    "omitted-xor-tree-leaf", "zero-real-exponential", "unscaled-exponential-shift",
}
PRINCIPAL = {
    "source_program_data", "source_interface_data", "source_fixed_grid_launch", "source_fixed_grid_correct",
    "source_fixed_grid_extract", "source_fixed_grid_rf", "source_canonical_correct", "source_canonical_extract",
    "source_canonical_output", "canonical_uniform", "source_uniform_output",
    "LarkNativeSoftmax.source_order_correct", "LarkReal.NativeSoftmax.canonical_correct",
    "LarkReal.NativeSoftmax.row_sum_exponentials", "LarkReal.NativeSoftmax.source_spec_canonical",
    "LarkReal.NativeSoftmax.source_denominator_pos", "LarkReal.NativeSoftmax.wave_sum_real",
    "LarkReal.NativeSoftmax.real_sum_truncate", "LarkReal.NativeSoftmax.source_output_canonical",
}
TRUE_CLAIMS = (
    "whole_kernel_execution_proved", "repaired_whole_grid_some_execution_proved",
    "repaired_whole_grid_race_freedom_proved", "repaired_whole_grid_all_outputs_proved",
    "canonical_source_equivalence_proved", "canonical_whole_grid_correct_proved",
    "positive_source_denominator_proved", "uniform_source_output_proved",
)
FALSE_CLAIMS = (
    "original_whole_grid_execution_proved", "registered_source_profile", "race_freedom_assumed",
    "conflict_witness_state_reachability_proved", "original_whole_block_race_freedom_proved",
    "ieee_equivalence_proved", "floating_point_error_bound_proved", "original_paper_fully_reproduced",
    "own_lean_compiled_cache_seeded",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_data(actual, expected):
    if type(expected) is dict:
        return type(actual) is dict and actual.keys() == expected.keys() and all(exact_data(actual[k], v) for k, v in expected.items())
    return type(actual) is type(expected) and actual == expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--dependency-project", type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    require(not any((p / ".git").exists() for p in (out, *out.parents)), "Choose output outside Git")
    require(shutil.which("git", path=str(lean_bin)) is None, "Git must be unavailable during replay")
    version = subprocess.check_output([str(lean_bin / "lean"), "--version"], text=True, timeout=30)
    require("version 4.19.0" in version, "Pinned Lean4.19.0 required")
    for name, digest in json.loads((packet / "manifest.json").read_text()).items():
        require(Path(name).name == name and sha(packet / name) == digest, "Packet hash/path differs")
    report = json.loads((packet / "results.json").read_text())
    require(report.get("status") == "native-softmax-source-bound-canonical-real-whole-grid-checked"
            and report.get("stage") == "canonical-real-whole-grid", "Wrong canonical-real proof stage")
    require(all(report.get(k) is True for k in TRUE_CLAIMS), "Missing canonical-real whole-grid claims")
    require(all(report.get(k) is False for k in FALSE_CLAIMS), "Invented IEEE/original/certificate/cache claim")
    expected = {
        "source_certificates": 0, "local_lean_modules": 134, "standard_lean_modules": 129, "real_lean_modules": 5,
        "rows": {"min": 1, "max": 42730}, "original_fuel": {"lane": 4096, "warp": 8, "block": 5, "grid": 1},
        "uniform_output": "1/50257", "whole_grid_variants": ["fixed"], "half_conversions": "identity",
        "reserved_seed": "arbitrary finite real", "real_exponential": "Real.exp", "mathlib_revision": MATHLIB,
        "external_pinned_mathlib_cache_seeded": True, "false_lean_claims_rejected": len(CONTROLS),
    }
    require(all(exact_data(report.get(k), v) for k, v in expected.items()), "Wrong canonical-real interpretation/counts/fuel")
    require(PRINCIPAL <= report["axiom_audits"].keys(), "Canonical-real principal audits absent")
    positives = {"frozen-reader", "fresh-real-library-build", "fresh-build"}
    require(len(report["checks"]) == len(positives | CONTROLS)
            and {c["name"] for c in report["checks"]} == positives | CONTROLS
            and all(c["expected_accepted"] is (c["name"] in positives)
                    and c["accepted"] is c["expected_accepted"] for c in report["checks"]), "Wrong canonical-real replay checks")
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
                    and entry.name not in seen and entry.name in source_manifest, "Unexpected archived source")
            total += entry.size
            require(entry.size <= 8_000_000 and total <= 50_000_000, "Source archive exceeds bounds")
            blob = archive.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == source_manifest[entry.name], "Source hash differs")
            destination = project / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(source_manifest) and not (project / ".lake").exists()
            and not any(project.rglob("*.olean")), "Unexpected own compiled cache")
    require(sum(n.endswith(".lean") and n.startswith("Lark/") for n in seen) == 129
            and sum(n.endswith(".lean") and n.startswith("LarkReal/") for n in seen) == 5, "Owned module closure differs")
    lock = json.loads((project / "lake-manifest.json").read_text())
    packages = lock["packages"]
    require(len(packages) == 9 and all(p["type"] == "git" for p in packages)
            and [p["rev"] for p in packages if p["name"] == "mathlib"] == [MATHLIB], "Wrong dependency lock")
    seeds, records = {}, []
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
        records.append({"name": name, "revision": package["rev"], "clean": True})
    require(records == report["dependency_sources_checked_before_path_restriction"], "Dependency source receipts differ")
    overrides = [dict(p, type="path", dir=str(seeds[p["name"]])) for p in packages]
    override_path = out / "dependency-path-overrides.json"
    override_path.write_text(json.dumps({"version": lock["version"], "packages": overrides}, indent=2) + "\n")
    lake = ["lake", "--packages=" + str(override_path)]
    env = dict(os.environ)
    env["PATH"] = str(lean_bin)
    env.pop("PYTHONPATH", None)
    env.pop("LEAN_PATH", None)
    env["PYTHONNOUSERSITE"] = "1"
    checks, logs = [], []
    for receipt in report["checks"]:
        name, expected_accepted = receipt["name"], receipt["expected_accepted"]
        command = ([sys.executable, "validate_source.py"] if name == "frozen-reader"
                   else lake + ["build", "LarkReal.NativeSoftmaxCanonical"] if name == "fresh-real-library-build"
                   else lake + ["build"] if name == "fresh-build"
                   else lake + ["env", "lean", name + ".lean"])
        before = time.monotonic()
        run = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=600)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        accepted = run.returncode == 0 and "error:" not in log and "sorryAx" not in log
        require(accepted is expected_accepted, "Unexpected acceptance: " + name + "\n" + log)
        if name in ("fresh-real-library-build", "fresh-build"):
            logs.append(log)
        if not expected_accepted:
            require("error:" in log and ("is false" in log or "⊢ False" in log)
                    and not any(s in log for s in ("maximum recursion", "maximum heartbeats", "maximum number of heartbeats",
                                                   "deep recursion", "Stack overflow")), "Wrong rejection gate: " + name)
        checks.append({"name": name, "accepted": accepted, "expected_accepted": expected_accepted,
                       "exit_code": run.returncode, "seconds": time.monotonic() - before, "timed_out": False})
    audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", "\n".join(logs)))
    require(audits == report["axiom_audits"], "Fresh axiom audits differ")
    require(all(set(a.strip() for a in ax.split(",") if a.strip()) <=
                {"propext", "Classical.choice", "Quot.sound"} for ax in audits.values()), "Extra axiom")
    result = {
        "schema": 1, "status": "frozen-softmax-canonical-real-whole-grid-archive-replayed",
        "source_archive_sha256": sha(packet / "source.tar.gz"), "packet_manifest_sha256": sha(packet / "manifest.json"),
        "local_lean_modules": 134, "axiom_audits": len(audits), "false_lean_claims_rejected": len(CONTROLS),
        "git_available_on_replay_path": False, "own_lean_compiled_cache_seeded": False,
        "external_pinned_mathlib_cache_seeded": True, "dependency_path_overrides_used": True,
        "original_git_lock_unchanged": True, "dependency_sources_checked_before_path_restriction": records,
        "checks": checks, "source_certificates": 0, "gpu_trials": 0, "model_calls": 0,
    }
    result.update({name: report[name] for name in set(TRUE_CLAIMS) | set(FALSE_CLAIMS) | set(expected)})
    (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "replay.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": 134, "audits": len(audits), "rejections": len(CONTROLS)}))


if __name__ == "__main__":
    main()
