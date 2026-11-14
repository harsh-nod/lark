"""Freeze six PTX kernels, the complete FFN pipeline and every earlier evidence byte.

This binds recorded publication, CI and promotion evidence. It performs no
Lean, model or GPU experiment and leaves every v27 snapshot byte unchanged.
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


BASELINE_AUDITOR_SHA256 = "544a11675a76bdf2eca245f1a1e289758d9bc8089e2e12a0e8db07f63027dab5"
ROOT = Path(__file__).resolve().parents[2]
BASELINE = "reproduction/paper_results/snapshots/20261113-v27"
BASELINE_MANIFEST = "aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0"
DEFINITIONS = {"reproduction/paper_results/audit.py", "reproduction/paper_results/targets.json"}
HISTORY = "reproduction/paper_results/frozen-definitions/20261113-v27"
EARLIER_DRAFT_RUNTIME = "reproduction/paper_results/runtime-definitions/20261114-v28"
RUNTIME = "reproduction/paper_results/runtime-definitions/20261114-v28-v2"
SOURCE_FILES = tuple("reproduction/paper_results/" + name for name in (
    "ptx_ffn_evidence.py", "ptx_ffn_protocol.json", "ptx_ffn_packet.py",
    "ptx_ffn_release.py", "ptx_ffn_release_protocol.json", "prepare_ptx_ffn_snapshot.py")) + (
    "reproduction/ptx/check_ffn_payloads.py", "reproduction/ptx/check_ffn_source_controls.py",
    "reproduction/ptx/check_ffn_recording_controls.py", ".github/workflows/ci.yml",
    "tests/test_ptx_ffn_release.py",
)
SPEC_KEYS = ("prefix", "receipt_prefix", "history_prefix", "ci_prefix", "ci_job_prefix",
             "publication_prefix", "ledger_publication_prefix")


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
    require(sha(folder / "manifest.json") == BASELINE_MANIFEST, "Immutable v27 snapshot differs")
    manifest = json.loads((folder / "manifest.json").read_text())
    require(all(sha(folder / name) == manifest[name] for name in (
        "evidence-manifest.json", "provenance.json", "targets.json", "auditor.py")),
        "Frozen v27 definitions or evidence bindings differ")
    original = json.loads((folder / "evidence-manifest.json").read_text())
    require(len(original) == 4135 and DEFINITIONS <= set(original), "Original v27 inventory differs")
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
        raise ValueError("Frozen v27 auditor integration point differs")
    additions = (
        ("    rotary_checks = check_ptx_rotary_evidence(config)\n",
         "    rotary_checks = check_ptx_rotary_evidence(config)\n"
         "    from ptx_ffn_release import check_ptx_ffn_evidence\n"
         "    ffn_checks = check_ptx_ffn_evidence(config)\n"),
        ('        "ptx_rotary_evidence_checks": rotary_checks,\n',
         '        "ptx_rotary_evidence_checks": rotary_checks,\n'
         '        "ptx_ffn_evidence_checks": ffn_checks,\n'),
        ('    rotary = report["ptx_rotary_evidence_checks"]\n',
         '    rotary = report["ptx_rotary_evidence_checks"]\n'
         '    ffn = report["ptx_ffn_evidence_checks"]\n'),
        ('        "ReLU, GEMV, GEMM, BMM, Linear and RoPE are six independent full-size PTX development "\n',
         '        link("reproduction/ptx/full-size/ffn/README.md",\n'
         '             "Complete source-bound compiled FP16 FFN pipeline")\n'
         '        + " adds both actual stateful launches and the shared 65536-value FP16 intermediate. "\n'
         '        + "The full 256/1024 reduction terms, 65536/16384 lanes and 16384 reference outputs "\n'
         '        + "retain their original contracts. Three local recordings and two hosted CI checks "\n'
         '        + "concern one pipeline identity. Four direct Lean dependency controls and 31 complete "\n'
         '        + "false recordings are custom controls. " + ffn["scope"] + "\\n",\n'
         '        "ReLU, GEMV, GEMM, BMM, Linear and RoPE are six independent full-size PTX development "\n'),
    )
    for before, after in additions:
        if source.count(before) != 1:
            raise ValueError("Frozen v27 auditor integration point differs")
        source = source.replace(before, after)
    compile(source, "frozen-six-kernel-and-FFN-pipeline-auditor.py", "exec")
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
    return {"status": "six-kernel-plus-FFN-frozen-inputs-staged-for-review", "files": sorted(files),
            "original_evidence_files_preserved": 4133, "fresh_Lean_GPU_model_experiments": 0}


def assemble_config(evidence_commit, root=ROOT):
    """Require complete committed inputs and retain each historical path/hash."""
    root = Path(root).resolve()
    protocol = read(root / "reproduction/paper_results/ptx_ffn_release_protocol.json")
    spec = {key: protocol[key] for key in SPEC_KEYS}
    prefixes = tuple(dict.fromkeys((*spec.values(), *protocol["declared_prefixes"])))
    require(all((root / prefix).is_dir() for prefix in prefixes)
            and all((root / name).is_file() for name in protocol["retained_files"]),
            "Complete FFN publication, source CI and retained history required")
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
                                     "--", *prefixes, HISTORY, EARLIER_DRAFT_RUNTIME, RUNTIME,
                                     *SOURCE_FILES, *protocol["matched_SDK_files"]],
                                    cwd=root, text=True).splitlines()
    require(all(any(n.startswith(prefix + "/") for n in later) for prefix in prefixes)
            and set(SOURCE_FILES) <= set(later)
            and expected_files | {RUNTIME + "/manifest.json"} <= set(later),
            "Complete committed FFN source, history and runtime captures required")
    config.update(evidence_commit=evidence_commit, storage_schema=2,
                  preserved_evidence_origins=selected, current_runtime_sources=aliases, ptx_ffn_proof=spec)
    groups = config["evidence_groups"]
    groups["later_artifacts"] = sorted(set(groups["later_artifacts"]) | set(later))
    groups["ptx_ffn_proof"] = sorted(set(SOURCE_FILES) | set(protocol["matched_SDK_files"])
        | set(aliases.values()) | {n for n in later if any(n.startswith(prefix + "/") for prefix in prefixes)})
    additions = {
        "tab:instr-cats": "The separate complete FFN pipeline covers both actual compiled PTX programs "
            "with 173/171 instructions, including all 256/1024 reduction terms, ReLU and half stores/loads.",
        "tab:task-configs": "FFN retains x[64,256], up[256,1024], hidden[64,1024], down[1024,256] "
            "and output[64,256], FP16, grids65536/16384, block1/warp32 and original CUDA fuel.",
        "tab:retarget": "The FFN pipeline adds one complete development pipeline with two source-bound "
            "stateful launches and four direct Lean dependency controls. No original sharing percentage is added.",
        "tab:trust": "FFN proves both actual-source executions, shared intermediate, independently defined "
            "tensor reference, race freedom and outside-footprint frame under abstract scalar/pointer/host "
            "interpretations. Three local and two CI checks concern one pipeline. Four direct and 31 false-recording "
            "controls are custom controls; all development failures remain retained. Only standard axioms are "
            "accepted. No IEEE/error bound, NVIDIA execution or original model result is added.",
    }
    for label, description in additions.items():
        row = config["floats"][label]
        row["available_evidence"] += " " + description
        row["evidence_groups"] = list(dict.fromkeys([*row["evidence_groups"], "ptx_ffn_proof"]))
    config["dependencies"]["semantics"] += (
        " A separate full-size FFN development pipeline now binds two actual compiled PTX launches, "
        "their full reductions and shared FP16 intermediate to an independent tensor reference. "
        "It is one pipeline identity alongside the six independently developed PTX kernels.")
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
    # The frozen auditor checks all six kernel packets, the FFN pipeline and model cohorts during
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
    ffn = report["ptx_ffn_evidence_checks"]
    require(ffn["independent_source_bound_development_pipelines"] == 1
            and len(ffn["recorded_positive_checks"]) == 3
            and ffn["recorded_source_CI_positive_builds"] == 2
            and ffn["recorded_direct_Lean_refusals"] == 4
            and len(ffn["independent_false_recording_refusals"]) == 31
            and ffn["successful_source_CI_jobs"] == 24
            and report["original_paper_fully_reproduced"] is False and report["completion_percentage"] is None,
            "Frozen complete FFN pipeline/original-result scope differs")
    return {"status": "six-kernel-and-complete-FFN-pipeline-ledger-prepared", "snapshot": str(snapshot),
            "original_evidence_files_preserved": len(original), "complete_independent_cohorts": 6,
            "FFN_pipeline_identities": 1, "FFN_local_recorded_checks": 3, "FFN_CI_checks": 2,
            "original_paper_fully_reproduced": False, "fresh_Lean_GPU_model_experiments": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage-inputs", action="store_true",
                        help="Capture both source versions for review and commit before building")
    parser.add_argument("--evidence-commit")
    parser.add_argument("--source-archive", type=Path)
    parser.add_argument("--snapshot", type=Path,
                        default=Path("reproduction/paper_results/snapshots/20261114-v28"))
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
