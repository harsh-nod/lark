"""Prepare a new paper ledger only from all six complete independent cohorts.

Existing snapshots are preserved. This checks recorded evidence and freezes a new
ledger; it runs no model, Lean or GPU experiment and does not publish anything.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.paper_results.full_shape_evidence import check_full_shape_evidence  # noqa: E402

BASELINE = "reproduction/paper_results/snapshots/20261112-v22"
DEFAULT_COMPARISON = "reproduction/local_models/results/full-shape-comparison-six-cohorts-v1"
METADATA = ("results.json", "raw-results.json", "audit-results.json", "binding.json",
            "cohort-files.json", "audit-files.json", "manifest.json")
LATER_ARTIFACTS = (
    "reproduction/paper_results/original-artifact-full-query-20261112",
    "reproduction/paper_results/original-artifact-refresh-20261113-0900",
    "reproduction/local_models/results/ptx-verifier-implementation-review-v1",
    "reproduction/ptx/results/full-size-compilation-v1",
    "reproduction/ptx/results/full-size-compilation-publication-v1",
    "reproduction/ptx/results/full-size-compilation-ci-v1",
    "reproduction/paper_results/level2-cost-arithmetic-v1",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def augment_auditor(source):
    """Extend the frozen v22 auditor without changing its existing checks."""
    substitutions = (
        ("    numerical_checks = check_numerical_evidence(config)\n",
         "    numerical_checks = check_numerical_evidence(config)\n"
         "    from full_shape_evidence import check_full_shape_evidence\n"
         "    model_checks = check_full_shape_evidence(config)\n"),
        ('        "numerical_evidence_checks": numerical_checks,\n',
         '        "numerical_evidence_checks": numerical_checks,\n'
         '        "full_shape_model_evidence_checks": model_checks,\n'),
        ('    text = [\n',
         '    models = report["full_shape_model_evidence_checks"]\n'
         '    verified = sum(row["counts"]["verified_within_budget"] for row in models["cohorts"])\n'
         '    requests = sum(row["counts"]["model_requests"] for row in models["cohorts"])\n'
         '    text = [\n'),
        ('        "| Paper item / source label | Role and assessment | Available evidence / scope | Missing inputs |",\n',
         '        "The later full-size comparison supplies "\n'
         '        + str(models["complete_independent_cohorts"])\n'
         '        + " complete independent model/language cohorts, " + str(verified)\n'
         '        + " verified proofs and " + str(requests) + " recorded responses. "\n'
         '        + models["scope"],\n'
         '        link(report["evidence_groups"]["full_shape_models"][0],\n'
         '             "Full-size comparison") + ".\\n",\n'
         '        "| Paper item / source label | Role and assessment | Available evidence / scope | Missing inputs |",\n'),
        ('        "The broader repository query returns 256 results and inspects only its first 30;",\n'
         '        "this bounded check does not establish absence from other results or sources.",\n',
         '        "An earlier bounded query inspected 30 of 256 returned results. A later",\n'
         '        "November12 query retrieved all 256 results for that one query; this",\n'
         '        "does not establish absence from other terms, sources, branches or repositories.",\n'
         '        link("reproduction/paper_results/original-artifact-full-query-20261112/results.json",\n'
         '             "Complete pages for that bounded query") + ".\\n",\n'
         '        link("reproduction/paper_results/original-artifact-refresh-20261113-0900/results.json",\n'
         '             "November13 bounded observations") + " and "\n'
         '        + link("reproduction/local_models/results/ptx-verifier-implementation-review-v1/results.json",\n'
         '               "PTX implementation review")\n'
         '        + " retain their separate source/observation scopes; no whole-launch LARK bridge is established.\\n",\n'),
        ('    text += ["\\n## Concrete dependencies\\n"]\n',
         '    text += [\n'
         '        link("reproduction/ptx/results/full-size-compilation-v1/RESULTS.md",\n'
         '             "Full-size CPU PTX assembly")\n'
         '        + " records 25 assembled source stages across 17 independent tasks. "\n'
         '        + "The current reader refuses every generated program; no full-size PTX "\n'
         '        + "proof, model success or NVIDIA execution is added.\\n",\n'
         '        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n'
         '             "Published Level-2 table arithmetic")\n'
         '        + " records GLM totals that match all-task means rather than the "\n'
         '        + "successful-task rule in the caption; no original model logs are recovered.\\n",\n'
         '        "\\n## Concrete dependencies\\n",\n'
         '    ]\n'),
    )
    for old, new in substitutions:
        require(source.count(old) == 1, "Frozen v22 auditor integration point differs")
        source = source.replace(old, new)
    compile(source, "frozen-full-shape-auditor.py", "exec")
    return source


def prepare_snapshot(*, evidence_commit, comparison_prefix, source_archive, snapshot, root=ROOT):
    root = Path(root).resolve()
    comparison = PurePosixPath(comparison_prefix)
    require(not comparison.is_absolute() and ".." not in comparison.parts
            and str(comparison) == comparison_prefix, "Unsafe comparison path")
    report = read(root / comparison_prefix / "results.json")
    # Check this before creating anything, checking out code, or running validators.
    require(report["expected_independent_cohorts"] == report["complete_independent_cohorts"] == 6
            and report["all_six_independent_cohorts_present"] is True
            and report["missing_cohorts"] == [] and len(report["inputs"]) == 6
            and report["original_paper_fully_reproduced"] is False,
            "All six complete independent cohorts are required before snapshot creation")
    require(re.fullmatch(r"[0-9a-f]{40}", evidence_commit) is not None,
            "Concrete full source checkpoint required")
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            == evidence_commit
            and not subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip(),
            "Source checkout must be clean at the concrete evidence checkpoint")
    snapshot = Path(snapshot)
    snapshot = (root / snapshot).resolve() if not snapshot.is_absolute() else snapshot.resolve()
    require(snapshot.is_relative_to(root / "reproduction/paper_results/snapshots")
            and not snapshot.exists(), "Fresh snapshot inside the repository required")
    config = copy.deepcopy(read(root / BASELINE / "targets.json"))
    archive = Path(source_archive).resolve()
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == config["source_archive_sha256"],
            "Pinned original manuscript archive required")
    config["evidence_commit"] = evidence_commit
    paths = [comparison_prefix + "/" + name for name in
             ("RESULTS.md", "results.json", "binding.json", "manifest.json")]
    driver = read(root / comparison_prefix / "binding.json")["driver_source_path"]
    paths += [driver, "reproduction/paper_results/full_shape_evidence.py"]
    packets = []
    for row in report["inputs"]:
        prefix = "reproduction/local_models/results/" + row["packet_id"]
        packets.append({"prefix": prefix, "manifest_sha256": row["packet_manifest_sha256"]})
        paths += [prefix + "/" + name for name in METADATA]
    config["evidence_groups"]["full_shape_models"] = paths
    config["full_shape_models"] = {"comparison_prefix": comparison_prefix,
                                    "required_cohorts": 6, "packets": packets}
    later = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", evidence_commit,
                                     "--", *LATER_ARTIFACTS], cwd=root, text=True).splitlines()
    require(all(any(name.startswith(prefix + "/") for name in later)
                for prefix in LATER_ARTIFACTS), "Later artifact observations missing")
    config["evidence_groups"]["later_artifacts"] = later
    model_checks = check_full_shape_evidence(config, root=root)
    from reproduction.local_models import compare_full_shape
    fresh = compare_full_shape.compare([root / item["prefix"] for item in packets])
    require({k: v for k, v in fresh.items() if k != "created_at_utc"}
            == {k: v for k, v in report.items() if k != "created_at_utc"}
            and compare_full_shape.markdown(fresh)
            == (root / comparison_prefix / "RESULTS.md").read_text(),
            "Complete comparison must regenerate from its raw and fresh-audit packets")
    descriptions = {
        "tab:main-results": "Six independent full-size HIP/CUDA cohorts cover three pinned open checkpoints. "
            "Per-level successful-task token means and all-task totals are checked; fixed proof slots and "
            "generic libraries differ from the original registry, agent and model matrix.",
        "tab:verify-model": "The five independent Level-2 shapes now have complete model outcomes for three "
            "checkpoints and both source languages. Attention remains dense SDPA; original FlashAttention, "
            "optimized Level-2 PTX and original model histories are unavailable. A separate arithmetic "
            "check finds that displayed GLM totals match all-task means rather than the caption's "
            "successful-task rule; both calculations are retained without changing manuscript values.",
        "tab:kernelcraft-model-budgets": "The independent protocol uses sixteen responses, eight source reads "
            "and three actual Lean checks per task, with explicit context/output/time limits. Original "
            "settings remain manuscript metadata; no original hosted-model dollar ceiling is simulated.",
        "tab:eval-main-res": "The six independent cohorts contain 102 full-size fixed-scaffold tasks "
            "including 72 Level-1 tasks. They do not reproduce the original four-model, three-language "
            "144-cell Level-1 matrix; these totals are not a paper-completion denominator.",
        "tab:stage-cost": "Every independent request and reported prompt/completion cost is retained and "
            "reconciled. Source reads and four fixed proof slots do not match the original segmentation, "
            "equivalence, diagnosis or cached-dialogue stage accounting.",
        "tab:analyst-cost": "Independent failed proposals, failed Lean candidates and their costs remain "
            "archived. They supply no original analyst, probe, second-opinion or diagnosis-call census.",
        "fig:model-size": "The complete categorical three-checkpoint, two-source full-size comparison is "
            "published. Different architectures, templates, tokenizers and serving precision prevent an "
            "isolated causal model-size conclusion or recovery of original figure values.",
    }
    for label, description in descriptions.items():
        row = config["floats"][label]
        row["available_evidence"] = description
        row["evidence_groups"] = list(dict.fromkeys([*row["evidence_groups"], "full_shape_models"]))
    config["dependencies"]["runs"] = (
        "Original request/response and checker traces, original model revisions and hosted-model outcomes. "
        "Six independent fixed-scaffold open-model cohorts on AMD are additional evidence; offline/free "
        "inference does not recover the original paid or closed-model histories.")
    config["evidence_links"] = {
        name: "https://github.com/harsh-nod/lark/blob/" + evidence_commit + "/" + name
        for group in config["evidence_groups"].values() for name in group}
    auditor = augment_auditor((root / BASELINE / "auditor.py").read_text())
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / "auditor.py").write_text(auditor)
    write(snapshot / "targets.json", config)
    subprocess.run([sys.executable, str(root / "reproduction/paper_results/replay_snapshot.py"),
                    "--snapshot", str(snapshot), "--source-archive", str(archive), "--build"],
                   cwd=root, check=True, timeout=600)
    return {"status": "six-cohort-paper-ledger-snapshot-prepared", "snapshot": str(snapshot),
            "complete_independent_cohorts": model_checks["complete_independent_cohorts"],
            "original_paper_fully_reproduced": False, "fresh_Lean_GPU_model_experiments": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-commit", required=True)
    parser.add_argument("--comparison-prefix", default=DEFAULT_COMPARISON)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--snapshot", type=Path,
                        default=Path("reproduction/paper_results/snapshots/20261113-v23"))
    print(json.dumps(prepare_snapshot(**vars(parser.parse_args()))))


if __name__ == "__main__":
    main()
