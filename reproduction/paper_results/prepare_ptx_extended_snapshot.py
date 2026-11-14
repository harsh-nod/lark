"""Freeze five independent PTX development proofs and every earlier evidence byte.

This assembles recorded results after actual publication, CI and main receipts
exist. It performs no Lean, model or GPU experiment and leaves v25 unchanged.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.paper_results.full_shape_evidence import check_full_shape_evidence  # noqa: E402
from reproduction.paper_results.ptx_pointwise_evidence import check_ptx_pointwise_evidence  # noqa: E402
from reproduction.paper_results.ptx_dot_evidence import check_ptx_dot_evidence  # noqa: E402
from reproduction.paper_results.ptx_matrix_evidence import check_ptx_matrix_evidence  # noqa: E402
from reproduction.paper_results.ptx_extended_evidence import (  # noqa: E402
    CONFIG_KEYS, PROTOCOLS, check_ptx_batched_evidence, check_ptx_linear_evidence,
)

BASELINE = "reproduction/paper_results/snapshots/20261113-v25"
BASELINE_MANIFEST = "e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f"
HISTORY = "reproduction/paper_results/frozen-definitions/20261113-v25"
REQUIRED = tuple(p[key] for p in PROTOCOLS.values()
                 for key in ("prefix", "publication_prefix", "ci_prefix", "main_prefix")) + (
    "reproduction/paper_results/snapshot-v25-ci-main-v1",
    "reproduction/paper_results/original-artifact-observation-bmm-20261113-v1",
    "reproduction/paper_results/snapshot-v26-format-compatibility-v1",
    "reproduction/paper_results/snapshot-v26-stream-compatibility-v1",
    "reproduction/paper_results/snapshot-v26-ptx-reader-validation-v1",
    "reproduction/paper_results/snapshot-v26-control-storage-validation-v1",
)
SOURCE_FILES = tuple("reproduction/paper_results/" + name for name in (
    "ptx_extended_evidence.py", "ptx_extended_protocols.json", "snapshot_archives.py",
    "snapshot_control_archives.py", "replay_snapshot.py", "check_snapshot_controls.py",
    "check_public_snapshot.py", "prepare_ptx_extended_snapshot.py", "PTX_LEDGER_READERS.md",
    "ARCHIVE_FORMAT.md")) + tuple("tests/" + name for name in (
    "test_ptx_extended_paper_evidence.py", "test_snapshot_archives.py",
    "test_snapshot_control_archives.py", "test_public_snapshot_roster.py",
    "test_prepare_ptx_extended_snapshot.py"))


def require(condition, message):
    if not condition:
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


def check_retained_evidence(config, root=ROOT):
    root = Path(root)
    require(sha(root / BASELINE / "manifest.json") == BASELINE_MANIFEST, "Immutable v25 snapshot differs")
    original = read(root / BASELINE / "evidence-manifest.json")
    definitions = {"reproduction/paper_results/audit.py", "reproduction/paper_results/targets.json"}
    evidence = {n: value for n, value in original.items() if n not in definitions}
    require(len(original) == 3625 and len(evidence) == 3623, "Original v25 evidence inventory differs")
    declared = {p for group in config["evidence_groups"].values() for p in group}
    require(set(evidence) <= declared, "Every earlier evidence member must remain declared")
    for name, digest in evidence.items():
        require((root / name).is_file() and not (root / name).is_symlink() and sha(root / name) == digest,
                "Earlier evidence bytes differ: " + name)
    for name, canonical in (("auditor.py", "audit.py"), ("targets.json", "targets.json")):
        path = root / HISTORY / name
        require(path.is_file() and path.read_bytes() == (root / BASELINE / name).read_bytes()
                and sha(path) == original["reproduction/paper_results/" + canonical],
                "Original frozen definition was not retained byte-identically")
    return evidence


def augment_auditor(source):
    require(hashlib.sha256(source.encode()).hexdigest()
            == "5dfb6d20e2a3d52654eb24f9a53a5bc7379fca6af2f1e876dcea751dd6df1ab5",
            "Frozen v25 auditor integration point differs")
    additions = (
        ("    gemm_checks = check_ptx_matrix_evidence(config)\n",
         "    gemm_checks = check_ptx_matrix_evidence(config)\n"
         "    from ptx_extended_evidence import check_ptx_batched_evidence, check_ptx_linear_evidence\n"
         "    bmm_checks = check_ptx_batched_evidence(config)\n"
         "    linear_checks = check_ptx_linear_evidence(config)\n"),
        ('        "ptx_matrix_evidence_checks": gemm_checks,\n',
         '        "ptx_matrix_evidence_checks": gemm_checks,\n'
         '        "ptx_batched_evidence_checks": bmm_checks,\n'
         '        "ptx_linear_evidence_checks": linear_checks,\n'),
        ('    gemm = report["ptx_matrix_evidence_checks"]\n',
         '    gemm = report["ptx_matrix_evidence_checks"]\n'
         '    bmm = report["ptx_batched_evidence_checks"]\n'
         '    linear = report["ptx_linear_evidence_checks"]\n'),
        ('        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n',
         '        link("reproduction/ptx/results/full-size-bmm-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 BMM proof")\n'
         '        + " adds one independent 32-batch [32,64,256] by [32,256,512] development kernel. "\n'
         '        + "All 138 instructions, sixteen real loop iterations and 1048576 active lanes are covered. "\n'
         '        + str(bmm["retained_positive_Main_checks"])\n'
         '        + " official positive Main recordings comprise four current-SDK checks and one earlier "\n'
         '        + "successful SDK renderer. One failed official export and cached development checks "\n'
         '        + "remain separate; no failed or partial check is counted as an accepted proof. "\n'
         '        + bmm["scope"] + "\\n",\n'
         '        link("reproduction/ptx/results/full-size-linear-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 Linear proof")\n'
         '        + " adds one independent [64,256] by [256,512] plus bias[512] development kernel. "\n'
         '        + "All 179 instructions and 32768 active lanes are covered, with bias added before "\n'
         '        + "the final half conversion. Its " + str(linear["retained_positive_Main_checks"])\n'
         '        + " official Main recordings are repeated checks of the same kernel. All twelve "\n'
         '        + "earlier development attempts, including five failures, remain separate. "\n'
         '        + linear["scope"] + "\\n",\n'
         '        "ReLU, GEMV, GEMM, BMM and Linear are five independent full-size PTX development "\n'
         '        + "kernels. Their current source-only recordings cover full actual-source execution, "\n'
         '        + "closed reference extraction, actual-trace race freedom and outside-output memory "\n'
         '        + "preservation within each declared abstract scalar model. They add no original "\n'
         '        + "model success, optimized program, hardware conformance or paper-completion result.\\n",\n'
         '        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n'),
    )
    for before, after in additions:
        require(source.count(before) == 1, "Frozen v25 auditor integration point differs")
        source = source.replace(before, after)
    compile(source, "frozen-five-PTX-development-proof-auditor.py", "exec")
    return source


def prepare_snapshot(*, evidence_commit, source_archive, snapshot, root=ROOT):
    root = Path(root).resolve()
    require(all((root / prefix / "manifest.json").is_file() for prefix in REQUIRED),
            "Complete BMM/Linear publication, source CI, main and validation receipts required")
    require(re.fullmatch("[0-9a-f]{40}", evidence_commit) is not None, "Concrete evidence checkpoint required")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == evidence_commit
            and not subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip(),
            "Clean concrete evidence checkout required")
    snapshot = Path(snapshot)
    snapshot = (root / snapshot).resolve() if not snapshot.is_absolute() else snapshot.resolve()
    require(snapshot.is_relative_to(root / "reproduction/paper_results/snapshots") and not snapshot.exists(),
            "Fresh snapshot inside repository required")
    config = copy.deepcopy(read(root / BASELINE / "targets.json"))
    manuscript = Path(source_archive).resolve()
    require(sha(manuscript) == config["source_archive_sha256"], "Pinned original manuscript source required")
    original = check_retained_evidence(config, root)
    config.update(evidence_commit=evidence_commit, storage_schema=2)
    later = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", evidence_commit,
                                     "--", *REQUIRED, HISTORY, *SOURCE_FILES], cwd=root, text=True).splitlines()
    require(all(any(n.startswith(prefix + "/") for n in later) for prefix in REQUIRED)
            and set(SOURCE_FILES) <= set(later)
            and {HISTORY + "/auditor.py", HISTORY + "/targets.json"} <= set(later),
            "Complete source, history and receipt checkpoint required")
    groups = config["evidence_groups"]
    groups["later_artifacts"] = sorted(set(groups["later_artifacts"]) | set(later))
    for kind, protocol in PROTOCOLS.items():
        spec = {k: protocol[k] for k in ("prefix", "publication_prefix", "ci_prefix", "main_prefix")}
        config[CONFIG_KEYS[kind]] = spec
        groups[CONFIG_KEYS[kind]] = ["reproduction/paper_results/ptx_extended_evidence.py",
            "reproduction/paper_results/ptx_extended_protocols.json",
            *[n for n in later if any(n.startswith(prefix + "/") for prefix in spec.values())]]
    check_retained_evidence(config, root)
    bmm = check_ptx_batched_evidence(config, root)
    linear = check_ptx_linear_evidence(config, root)
    check_ptx_matrix_evidence(config, root)
    check_ptx_dot_evidence(config, root)
    check_ptx_pointwise_evidence(config, root)
    models = check_full_shape_evidence(config, root)
    require(models["complete_independent_cohorts"] == 6 and models["all_six_independent_cohorts_present"] is True,
            "All six independent model cohorts required")
    from reproduction.local_models import compare_full_shape
    model_spec = config["full_shape_models"]
    fresh = compare_full_shape.compare([root / item["prefix"] for item in model_spec["packets"]])
    recorded = read(root / model_spec["comparison_prefix"] / "results.json")
    require({k: v for k, v in fresh.items() if k != "created_at_utc"}
            == {k: v for k, v in recorded.items() if k != "created_at_utc"}
            and compare_full_shape.markdown(fresh) == (root / model_spec["comparison_prefix"] / "RESULTS.md").read_text(),
            "All six complete raw/audit model packets must regenerate the comparison")
    additions = {
        "tab:instr-cats": "Subsequent full-size BMM and Linear development proofs cover all 138 and 179 "
            "compiled instructions respectively, including actual backward loops, BMM batch addressing "
            "and Linear's signed conversion and 64-bit shift. Other families and the authors' optimized "
            "instruction registry remain gaps.",
        "tab:task-configs": "BMM preserves [32,64,256] @ [32,256,512] -> [32,64,512] FP16, grid1048576; "
            "Linear preserves [64,256] @ [256,512] + bias[512] -> [64,512] FP16, grid32768. Both retain "
            "block1/warp32 and separate unchanged CUDA fuel[1030,1,1,1].",
        "tab:retarget": "The additional BMM and Linear readers extend exact-source development coverage "
            "to batch indexing, signed conversion and 64-bit shift, with four accepted-grammar Lean "
            "source-binding refusals each. No original code-sharing percentage or history is established.",
        "tab:trust": "BMM and Linear cover full actual-source launch execution, closed reference AST "
            "extraction, actual-trace race freedom and preservation outside output. Four current source-only "
            "checks each rebuild eight and ten owned modules; accepted audits use only standard axioms. "
            "BMM's earlier successful renderer and failed export and all twelve earlier Linear attempts "
            "remain retained with distinct counts. Parsing/reference formalization, scalar correspondence "
            "and aligned disjoint non-wrapping allocations remain trusted. No IEEE, NVIDIA or original-result "
            "claim is made.",
    }
    for label, description in additions.items():
        row = config["floats"][label]
        row["available_evidence"] += " " + description
        row["evidence_groups"] = list(dict.fromkeys([*row["evidence_groups"], *CONFIG_KEYS.values()]))
    before = "Together with ReLU and GEMV these are three independent development kernels, each with four retained checks."
    require(config["dependencies"]["semantics"].count(before) == 1, "Previous PTX kernel summary differs")
    config["dependencies"]["semantics"] = config["dependencies"]["semantics"].replace(before,
        "With the subsequent complete BMM and Linear proofs there are five independent full-size PTX "
        "development kernels. Each has four current source-only checks; BMM also retains an earlier official "
        "success and one failed official export, separately from cached/partial development history.")
    config["evidence_links"] = {n: "https://github.com/harsh-nod/lark/blob/" + evidence_commit + "/" + n
                                for group in groups.values() for n in group}
    require(not config["local_evidence"], "All evidence must have concrete committed source links")
    auditor = augment_auditor((root / BASELINE / "auditor.py").read_text())
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / "auditor.py").write_text(auditor)
    write(snapshot / "targets.json", config)
    subprocess.run([sys.executable, str(root / "reproduction/paper_results/replay_snapshot.py"),
                    "--snapshot", str(snapshot), "--source-archive", str(manuscript), "--build"],
                   cwd=root, check=True, timeout=600)
    layout = read(snapshot / "evidence-layout.json")
    require(all(layout["logical_files"][n]["sha256"] == digest for n, digest in original.items()),
            "Frozen earlier logical bytes changed")
    return {"status": "five-independent-PTX-development-proof-ledger-prepared", "snapshot": str(snapshot),
            "original_evidence_files_preserved": len(original), "complete_independent_cohorts": 6,
            "BMM_recorded_checks": bmm["retained_positive_Main_checks"],
            "Linear_recorded_checks": linear["retained_positive_Main_checks"],
            "original_paper_fully_reproduced": False, "fresh_Lean_GPU_model_experiments": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-commit", required=True)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--snapshot", type=Path,
                        default=Path("reproduction/paper_results/snapshots/20261113-v26"))
    print(json.dumps(prepare_snapshot(**vars(parser.parse_args()))))


if __name__ == "__main__":
    main()
