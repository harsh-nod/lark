"""Freeze six independent PTX development proofs and every earlier evidence byte.

This binds recorded publication, CI and promotion evidence. It performs no
Lean, model or GPU experiment and leaves every v26 snapshot byte unchanged.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

if __package__:
    from .replay_snapshot import committed_evidence, preserved_origins
else:
    from replay_snapshot import committed_evidence, preserved_origins


BASELINE_AUDITOR_SHA256 = "7ecd1972d1046c730fda5b28f9eda8bf804122507042dfd2b7a0b7c9273b62cf"
ROOT = Path(__file__).resolve().parents[2]
BASELINE = "reproduction/paper_results/snapshots/20261113-v26"
BASELINE_MANIFEST = "251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed"
DEFINITIONS = {"reproduction/paper_results/audit.py", "reproduction/paper_results/targets.json"}
HISTORY = "reproduction/paper_results/frozen-definitions/20261113-v26"
RUNTIME = "reproduction/paper_results/runtime-definitions/20261113-v27"
SOURCE_FILES = tuple("reproduction/paper_results/" + name for name in (
    "ptx_rotary_evidence.py", "ptx_rotary_protocol.json", "ptx_rotary_release.py",
    "ptx_rotary_release_protocol.json", "prepare_ptx_rotary_snapshot.py")) + (
    "reproduction/ptx/ROTARY.md",
) + tuple("tests/" + name for name in (
    "test_ptx_rotary_paper_evidence.py", "test_ptx_rotary_release.py",
    "test_prepare_ptx_rotary_snapshot.py", "test_snapshot_preserved_origins.py",
)) + (".github/workflows/ci.yml",)
SPEC_KEYS = ("prefix", "publication_prefix", "ci_prefix", "main_prefix")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for data in iter(lambda: source.read(1024 * 1024), b""):
            value.update(data)
    return value.hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def baseline_evidence(root):
    folder = Path(root) / BASELINE
    require(sha(folder / "manifest.json") == BASELINE_MANIFEST, "Immutable v26 snapshot differs")
    manifest = json.loads((folder / "manifest.json").read_text())
    require(all(sha(folder / name) == manifest[name] for name in (
        "evidence-manifest.json", "provenance.json", "targets.json", "auditor.py")),
        "Frozen v26 definitions or evidence bindings differ")
    original = json.loads((folder / "evidence-manifest.json").read_text())
    require(len(original) == 3794 and DEFINITIONS <= set(original), "Original v26 inventory differs")
    return {n: digest for n, digest in original.items() if n not in DEFINITIONS}


def preservation_plan(root=ROOT):
    """Retain every old path, selecting its original blob when runtime code evolved."""
    root = Path(root)
    current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    origins = json.loads((root / BASELINE / "provenance.json").read_text())["sources"]
    result = {}
    for name, expected in baseline_evidence(root).items():
        path = root / name
        require(path.is_file() and not path.is_symlink(), "Earlier evidence file missing: " + name)
        if sha(path) == expected:
            continue
        source = origins[name]
        require(source["kind"] == "git-blob" and source["path"] == name,
                "Earlier evidence has no original committed path: " + name)
        binding = {"commit": source["commit"], "sha256": expected}
        committed_evidence(name, current, {name: binding}, root=root)
        result[name] = binding
    return result


def check_retained_evidence(config, root=ROOT):
    root = Path(root)
    original = baseline_evidence(root)
    names = {n for group in config["evidence_groups"].values() for n in group}
    require(set(original) <= names, "Every earlier evidence member must remain declared")
    selected = preserved_origins(config, names, set(config["local_evidence"]))
    current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    for name, expected in original.items():
        if name in selected:
            require(selected[name]["sha256"] == expected, "Earlier evidence binding differs: " + name)
            data, _ = committed_evidence(name, current, selected, root=root)
            require(hashlib.sha256(data).hexdigest() == expected, "Earlier evidence bytes differ: " + name)
        else:
            require((root / name).is_file() and not (root / name).is_symlink()
                    and sha(root / name) == expected, "Earlier evidence bytes differ: " + name)
    return original


def augment_auditor(source):
    if hashlib.sha256(source.encode()).hexdigest() != BASELINE_AUDITOR_SHA256:
        raise ValueError("Frozen v26 auditor integration point differs")
    additions = (
        ("    linear_checks = check_ptx_linear_evidence(config)\n",
         "    linear_checks = check_ptx_linear_evidence(config)\n"
         "    from ptx_rotary_release import check_ptx_rotary_evidence\n"
         "    rotary_checks = check_ptx_rotary_evidence(config)\n"),
        ('        "ptx_linear_evidence_checks": linear_checks,\n',
         '        "ptx_linear_evidence_checks": linear_checks,\n'
         '        "ptx_rotary_evidence_checks": rotary_checks,\n'),
        ('    linear = report["ptx_linear_evidence_checks"]\n',
         '    linear = report["ptx_linear_evidence_checks"]\n'
         '    rotary = report["ptx_rotary_evidence_checks"]\n'),
        ('        "ReLU, GEMV, GEMM, BMM and Linear are five independent full-size PTX development "\n',
         '        link("reproduction/ptx/results/full-size-rotary-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 interleaved RoPE proof")\n'
         '        + " adds one independent [256,128] development kernel with [256,64] sine/cosine "\n'
         '        + "inputs. All 51 instructions and 32768 lanes are covered, including initialized "\n'
         '        + "predicates, both branch paths, five actual memory accesses per lane and an "\n'
         '        + "independently defined reshape/select/stack/arithmetic/half tensor reference. Its "\n'
         '        + str(rotary["retained_positive_Main_checks"]) + " retained Main checks and "\n'
         '        + str(rotary["positive_rechecks"]) + " rechecks concern the same kernel. All "\n'
         '        + str(rotary["development_attempts"]) + " earlier development attempts, including "\n'
         '        + str(rotary["failed_development_checks"]) + " failures, remain separate. "\n'
         '        + rotary["scope"] + "\\n",\n'
         '        "ReLU, GEMV, GEMM, BMM, Linear and RoPE are six independent full-size PTX development "\n'),
    )
    for before, after in additions:
        if source.count(before) != 1:
            raise ValueError("Frozen v26 auditor integration point differs")
        source = source.replace(before, after)
    compile(source, "frozen-six-PTX-development-proof-auditor.py", "exec")
    return source


def stage_inputs(root=ROOT):
    """Prepare reviewable source captures to commit before freezing a checkpoint.

    Old logical paths retain their old bytes. Changed runtime source is also
    recorded under new paths, so both versions remain available to a reader.
    Existing captures are never overwritten with different bytes.
    """
    root = Path(root).resolve()
    baseline_evidence(root)
    selected = preservation_plan(root)
    files = {HISTORY + "/" + name: (root / BASELINE / name).read_bytes()
             for name in ("auditor.py", "targets.json")}
    aliases = {name: RUNTIME + "/" + name for name in selected}
    files.update({alias: (root / name).read_bytes() for name, alias in aliases.items()})
    manifest = {"schema": 1, "baseline_manifest_sha256": BASELINE_MANIFEST,
                "preserved_evidence_origins": selected, "current_runtime_sources": aliases,
                "files": {name: hashlib.sha256(data).hexdigest() for name, data in sorted(files.items())}}
    files[RUNTIME + "/manifest.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    for name, data in files.items():
        path = root / name
        require(not path.is_symlink() and (not path.exists() or path.read_bytes() == data),
                "Existing frozen input differs: " + name)
    for name, data in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists():
            path.write_bytes(data)
    return {"status": "six-PTX-frozen-inputs-staged-for-review", "files": sorted(files),
            "original_evidence_files_preserved": 3792, "fresh_Lean_GPU_model_experiments": 0}


def assemble_config(evidence_commit, root=ROOT):
    """Require complete committed inputs and retain each historical path/hash."""
    root = Path(root).resolve()
    protocol = read(root / "reproduction/paper_results/ptx_rotary_release_protocol.json")
    spec = {key: protocol[key] for key in SPEC_KEYS}
    prefixes = (*spec.values(), *protocol["retained_history_manifests"])
    require(all((root / prefix / "manifest.json").is_file() for prefix in prefixes),
            "Complete RoPE publication, source CI, main and retained history required")
    config = copy.deepcopy(read(root / BASELINE / "targets.json"))
    selected = preservation_plan(root)
    capture = read(root / RUNTIME / "manifest.json")
    aliases = {name: RUNTIME + "/" + name for name in selected}
    expected_files = {HISTORY + "/" + name for name in ("auditor.py", "targets.json")} | set(aliases.values())
    require(capture == {"schema": 1, "baseline_manifest_sha256": BASELINE_MANIFEST,
                        "preserved_evidence_origins": selected, "current_runtime_sources": aliases,
                        "files": {name: sha(root / name) for name in sorted(expected_files)}},
            "Complete frozen definitions and current runtime capture required")
    require(all((root / alias).read_bytes() == (root / name).read_bytes() for name, alias in aliases.items())
            and all((root / HISTORY / name).read_bytes() == (root / BASELINE / name).read_bytes()
                    for name in ("auditor.py", "targets.json")),
            "Frozen definitions or current runtime bytes differ")
    later = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", evidence_commit,
                                     "--", *prefixes, HISTORY, RUNTIME, *SOURCE_FILES],
                                    cwd=root, text=True).splitlines()
    require(all(any(n.startswith(prefix + "/") for n in later) for prefix in prefixes)
            and set(SOURCE_FILES) <= set(later)
            and expected_files | {RUNTIME + "/manifest.json"} <= set(later),
            "Complete committed RoPE source, history and runtime captures required")
    config.update(evidence_commit=evidence_commit, storage_schema=2,
                  preserved_evidence_origins=selected, ptx_rotary_proof=spec)
    groups = config["evidence_groups"]
    groups["later_artifacts"] = sorted(set(groups["later_artifacts"]) | set(later))
    groups["ptx_rotary_proof"] = [*SOURCE_FILES[:4], *[n for n in later
                                  if any(n.startswith(prefix + "/") for prefix in prefixes)]]
    additions = {
        "tab:instr-cats": "The compiled interleaved RoPE development proof covers all 51 instructions, "
            "including initialized predicates, both branches and five actual memory accesses per lane. "
            "General instruction coverage and the authors' optimized registry remain gaps.",
        "tab:task-configs": "RoPE retains x/output[256,128] and sine/cosine[256,64] FP16, "
            "grid32768/block1/warp32 and unchanged original CUDA fuel[8,1,1,1].",
        "tab:retarget": "RoPE adds one complete compiled PTX development proof and four direct "
            "accepted-grammar source-binding refusals. It establishes no original sharing percentage.",
        "tab:trust": "RoPE proves full actual-source execution, independently defined tensor-reference "
            "equality, actual-trace race freedom and outside-output memory preservation under abstract "
            "scalar operations. Four retained checks and three rechecks concern one kernel. Seventeen "
            "earlier development attempts, including eleven failures, remain separate. Only standard "
            "axioms are accepted. Parsing, ABI, scalar correspondence and allocation assumptions remain "
            "trusted; no IEEE/error bound, NVIDIA execution or original-paper result is added.",
    }
    for label, description in additions.items():
        row = config["floats"][label]
        row["available_evidence"] += " " + description
        row["evidence_groups"] = list(dict.fromkeys([*row["evidence_groups"], "ptx_rotary_proof"]))
    before = "With the subsequent complete BMM and Linear proofs there are five independent full-size PTX development kernels."
    require(config["dependencies"]["semantics"].count(before) == 1, "Previous PTX kernel summary differs")
    config["dependencies"]["semantics"] = config["dependencies"]["semantics"].replace(before,
        "With the subsequent complete BMM, Linear and interleaved RoPE proofs there are six independent "
        "full-size PTX development kernels. RoPE adds a separate 51-instruction, 32768-lane proof with "
        "an independent tensor reference and both actual branch paths.")
    config["evidence_links"] = {name: "https://github.com/harsh-nod/lark/blob/"
                                + selected.get(name, {}).get("commit", evidence_commit) + "/" + name
                                for names in groups.values() for name in names}
    require(not config["local_evidence"], "All evidence must have concrete committed source links")
    check_retained_evidence(config, root)
    return config


def prepare_snapshot(*, evidence_commit, source_archive, snapshot, root=ROOT):
    root = Path(root).resolve()
    require(re.fullmatch("[0-9a-f]{40}", evidence_commit) is not None, "Concrete evidence checkpoint required")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == evidence_commit
            and not subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip(),
            "Clean concrete evidence checkout required")
    snapshot = Path(snapshot)
    snapshot = (root / snapshot).resolve() if not snapshot.is_absolute() else snapshot.resolve()
    require(snapshot.is_relative_to(root / "reproduction/paper_results/snapshots") and not snapshot.exists(),
            "Fresh snapshot inside repository required")
    config = assemble_config(evidence_commit, root)
    manuscript = Path(source_archive).resolve()
    require(sha(manuscript) == config["source_archive_sha256"], "Pinned original manuscript source required")
    original = baseline_evidence(root)
    # The frozen auditor checks all six proof packets and model cohorts during
    # creation. No previously recorded experiment or CI workflow is rerun.
    auditor = augment_auditor((root / BASELINE / "auditor.py").read_text())
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / "auditor.py").write_text(auditor)
    write(snapshot / "targets.json", config)
    subprocess.run([sys.executable, str(root / "reproduction/paper_results/replay_snapshot.py"),
                    "--snapshot", str(snapshot), "--source-archive", str(manuscript), "--build"],
                   cwd=root, check=True, timeout=600)
    layout = read(snapshot / "evidence-layout.json")
    require(all(layout["logical_files"][name]["sha256"] == digest for name, digest in original.items()),
            "Frozen earlier logical bytes changed")
    report = read(snapshot / "results/audit.json")
    models = report["full_shape_model_evidence_checks"]
    require(models["complete_independent_cohorts"] == 6 and models["all_six_independent_cohorts_present"] is True,
            "All six independent model cohorts required")
    rotary = report["ptx_rotary_evidence_checks"]
    require(rotary["independent_source_bound_development_proofs"] == 1
            and rotary["retained_positive_Main_checks"] == 4 and rotary["positive_rechecks"] == 3
            and report["original_paper_fully_reproduced"] is False and report["completion_percentage"] is None,
            "Frozen six-kernel development/original-result scope differs")
    return {"status": "six-independent-PTX-development-proof-ledger-prepared", "snapshot": str(snapshot),
            "original_evidence_files_preserved": len(original), "complete_independent_cohorts": 6,
            "RoPE_recorded_checks": 4, "RoPE_rechecks": 3,
            "original_paper_fully_reproduced": False, "fresh_Lean_GPU_model_experiments": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage-inputs", action="store_true",
                        help="Capture both source versions for review and commit before building")
    parser.add_argument("--evidence-commit")
    parser.add_argument("--source-archive", type=Path)
    parser.add_argument("--snapshot", type=Path,
                        default=Path("reproduction/paper_results/snapshots/20261113-v27"))
    args = parser.parse_args()
    if args.stage_inputs:
        require(args.evidence_commit is None and args.source_archive is None,
                "Stage inputs separately before committing a clean evidence checkpoint")
        result = stage_inputs()
    else:
        require(args.evidence_commit is not None and args.source_archive is not None,
                "Build requires --evidence-commit and --source-archive")
        result = prepare_snapshot(evidence_commit=args.evidence_commit,
                                  source_archive=args.source_archive, snapshot=args.snapshot)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
