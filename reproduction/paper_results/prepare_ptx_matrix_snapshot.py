"""Extend v24 only after the complete GEMM publication, CI and main gates exist.

This freezes recorded evidence. It runs no model, Lean or GPU experiment and
keeps every earlier snapshot and evidence entry.
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
from reproduction.paper_results.ptx_matrix_evidence import (  # noqa: E402
    CI, PREFIX, PUBLICATION, check_ptx_matrix_evidence,
)

BASELINE = "reproduction/paper_results/snapshots/20261113-v24"
MAIN_RECEIPT = "reproduction/ptx/results/full-size-gemm-proof-ci-main-v1"
REQUIRED = (PREFIX, PUBLICATION, CI, MAIN_RECEIPT,
            "reproduction/paper_results/snapshot-v24-ci-main-v1",
            "reproduction/ptx/results/full-size-gemm-proof-publication-v1",
            "reproduction/ptx/results/full-size-gemm-proof-ci-failed-v1",
            "reproduction/ptx/results/full-size-gemm-proof-ci-failure-log-v1")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def augment_auditor(source):
    replacements = (
        ("    gemv_checks = check_ptx_dot_evidence(config)\n",
         "    gemv_checks = check_ptx_dot_evidence(config)\n"
         "    from ptx_matrix_evidence import check_ptx_matrix_evidence\n"
         "    gemm_checks = check_ptx_matrix_evidence(config)\n"),
        ('        "ptx_dot_evidence_checks": gemv_checks,\n',
         '        "ptx_dot_evidence_checks": gemv_checks,\n'
         '        "ptx_matrix_evidence_checks": gemm_checks,\n'),
        ('    gemv = report["ptx_dot_evidence_checks"]\n',
         '    gemv = report["ptx_dot_evidence_checks"]\n'
         '    gemm = report["ptx_matrix_evidence_checks"]\n'),
        ('        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n',
         '        link("reproduction/ptx/results/full-size-gemm-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 GEMM proof")\n'
         '        + " adds one independent 64x256 by 256x512 development proof covering all 171 instructions, "\n'
         '        + "the actual sixteen-iteration backward loop, all 32768 active lanes, actual-trace race "\n'
         '        + "freedom, every extracted reference output and preservation outside the output footprint. Its "\n'
         '        + str(gemm["positive_rechecks"]) + " positive rechecks and "\n'
         '        + str(gemm["direct_Lean_negative_controls"])\n'
         '        + " direct Lean source-binding controls remain repeated checks of one kernel. "\n'
         '        + gemm["scope"] + "\\n",\n'
         '        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n'),
    )
    for before, after in replacements:
        require(source.count(before) == 1, "Frozen v24 auditor integration point differs")
        source = source.replace(before, after)
    compile(source, "frozen-complete-PTX-GEMM-auditor.py", "exec")
    return source


def prepare_snapshot(*, evidence_commit, source_archive, snapshot, root=ROOT):
    root = Path(root).resolve()
    require(all((root / prefix / "manifest.json").is_file() for prefix in REQUIRED),
            "Complete actual GEMM publication, twenty-one-job CI and main receipts required")
    require(re.fullmatch("[0-9a-f]{40}", evidence_commit) is not None,
            "Concrete evidence checkpoint required")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == evidence_commit
            and not subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip(),
            "Clean concrete evidence checkout required")
    snapshot = Path(snapshot)
    snapshot = (root / snapshot).resolve() if not snapshot.is_absolute() else snapshot.resolve()
    require(snapshot.is_relative_to(root / "reproduction/paper_results/snapshots") and not snapshot.exists(),
            "Fresh snapshot inside repository required")
    config = copy.deepcopy(read(root / BASELINE / "targets.json"))
    archive = Path(source_archive).resolve()
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == config["source_archive_sha256"],
            "Pinned original manuscript source required")
    before = {p for group in config["evidence_groups"].values() for p in group}
    config["evidence_commit"] = evidence_commit
    later = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", evidence_commit,
                                     "--", *REQUIRED], cwd=root, text=True).splitlines()
    require(all(any(p.startswith(prefix + "/") for p in later) for prefix in REQUIRED),
            "Later receipts missing")
    config["evidence_groups"]["later_artifacts"] = sorted(
        set(config["evidence_groups"]["later_artifacts"]) | set(later))
    config["ptx_matrix_proof"] = {"prefix": PREFIX, "publication_prefix": PUBLICATION, "ci_prefix": CI}
    config["evidence_groups"]["ptx_matrix_proof"] = [
        "reproduction/paper_results/ptx_matrix_evidence.py",
        *[p for p in later if any(p.startswith(prefix + "/") for prefix in (PREFIX, PUBLICATION, CI))],
    ]
    require(before <= {p for group in config["evidence_groups"].values() for p in group},
            "All earlier evidence must be retained")
    gemm = check_ptx_matrix_evidence(config, root=root)
    check_ptx_dot_evidence(config, root=root)
    check_ptx_pointwise_evidence(config, root=root)
    models = check_full_shape_evidence(config, root=root)
    require(models["complete_independent_cohorts"] == 6
            and models["all_six_independent_cohorts_present"] is True,
            "All six actual independent cohorts required")
    from reproduction.local_models import compare_full_shape
    spec = config["full_shape_models"]
    fresh = compare_full_shape.compare([root / p["prefix"] for p in spec["packets"]])
    recorded = read(root / spec["comparison_prefix"] / "results.json")
    require({k: v for k, v in fresh.items() if k != "created_at_utc"}
            == {k: v for k, v in recorded.items() if k != "created_at_utc"}
            and compare_full_shape.markdown(fresh) == (root / spec["comparison_prefix"] / "RESULTS.md").read_text(),
            "All six raw and fresh-audit packets must regenerate the comparison")
    promotion = read(root / MAIN_RECEIPT / "results.json")
    require(promotion["source_checkpoint"] == gemm["source_commit"] and promotion["source_CI_jobs"] == 21
            and promotion["original_paper_fully_reproduced"] is False,
            "Actual completed GEMM main-promotion receipt required")
    descriptions = {
        "tab:instr-cats": "A subsequent complete compiled FP16 GEMM profile covers all 171 instructions, "
            "the actual sixteen-iteration backward loop and all 32768 active lanes. Remaining generated "
            "families, general instruction/signature coverage and original optimized PTX remain gaps.",
        "tab:task-configs": "The complete GEMM development proof preserves [64,256] @ [256,512] -> [64,512] "
            "FP16 buffers, grid32768/block1/warp32 and independent CUDA fuel[1030,1,1,1] as separate data.",
        "tab:retarget": "The full-size GEMM development reader adds five typed integer operations and a "
            "complete actual-source backward loop. This establishes no original code-sharing percentage "
            "or implementation history.",
        "tab:trust": "The full-size GEMM packet binds the complete source, closed reference, full launch, "
            "actual memory-trace race freedom, extracted outputs and preservation outside the output "
            "footprint. Four positive checks rebuild twenty owned modules; each checks 169 library and six "
            "Main axiom audits using only standard axioms. Four accepted-grammar source changes fail in "
            "Lean. Parsing/reference formalization, abstract scalar/ABI correspondence and aligned "
            "disjoint non-wrapping allocations remain trusted; no NVIDIA or original-result claim is made.",
    }
    for label, description in descriptions.items():
        row = config["floats"][label]
        row["available_evidence"] += " " + description
        row["evidence_groups"] = list(dict.fromkeys([*row["evidence_groups"], "ptx_matrix_proof"]))
    config["dependencies"]["semantics"] += (
        " The subsequent complete compiled GEMM proof covers 171 instructions, sixteen real backward-loop "
        "iterations, 32768 active lanes, actual-trace race freedom, all reference outputs and outside-output "
        "memory preservation. Together with ReLU and GEMV these are three independent development kernels, "
        "each with four retained checks. They add no model success, legacy profile or original paper result. "
        "Other full-size PTX families and original optimized programs remain gaps.")
    config["evidence_links"] = {name: "https://github.com/harsh-nod/lark/blob/" + evidence_commit + "/" + name
                                for group in config["evidence_groups"].values() for name in group}
    auditor = augment_auditor((root / BASELINE / "auditor.py").read_text())
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / "auditor.py").write_text(auditor)
    write(snapshot / "targets.json", config)
    subprocess.run([sys.executable, str(root / "reproduction/paper_results/replay_snapshot.py"),
                    "--snapshot", str(snapshot), "--source-archive", str(archive), "--build"],
                   cwd=root, check=True, timeout=600)
    return {"status": "three-independent-PTX-proof-ledger-prepared", "snapshot": str(snapshot),
            "complete_independent_cohorts": 6, "original_paper_fully_reproduced": False,
            "fresh_Lean_GPU_model_experiments": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-commit", required=True)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--snapshot", type=Path, default=Path("reproduction/paper_results/snapshots/20261113-v25"))
    print(json.dumps(prepare_snapshot(**vars(parser.parse_args()))))


if __name__ == "__main__":
    main()
