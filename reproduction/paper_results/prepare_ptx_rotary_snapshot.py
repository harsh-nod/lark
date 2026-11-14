"""Extend the frozen v26 auditor without changing its original-result assessments."""

import hashlib
import json
from pathlib import Path
import subprocess

if __package__:
    from .replay_snapshot import committed_evidence, preserved_origins
else:
    from replay_snapshot import committed_evidence, preserved_origins


BASELINE_AUDITOR_SHA256 = "7ecd1972d1046c730fda5b28f9eda8bf804122507042dfd2b7a0b7c9273b62cf"
ROOT = Path(__file__).resolve().parents[2]
BASELINE = "reproduction/paper_results/snapshots/20261113-v26"
BASELINE_MANIFEST = "251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed"
DEFINITIONS = {"reproduction/paper_results/audit.py", "reproduction/paper_results/targets.json"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
