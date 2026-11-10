"""Inventory the pinned preprint and bind its result ledger to published evidence.

This is an audit of source coverage and evidence files, not a rerun of Lean,
inference or GPU experiments. Interpretation of the source is in targets.json.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FLOAT = re.compile(
    r"\\begin\{(?P<kind>table\*?|figure\*?)\}(?P<body>.*?)"
    r"\\end\{(?P=kind)\}",
    re.DOTALL,
)
INPUT = re.compile(r"\\input\{([^}]+)\}")
LABEL = re.compile(r"\\label\{([^}]+)\}")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def manuscript(archive, config):
    require(
        digest(archive.read_bytes()) == config["source_archive_sha256"],
        "Unexpected manuscript archive; this audit is specific to arXiv v1",
    )
    files = {}
    with tarfile.open(archive) as bundle:
        for member in bundle:
            path = PurePosixPath(member.name)
            require(not path.is_absolute() and ".." not in path.parts, "Unsafe archive path")
            if member.isdir():
                continue
            require(
                member.isfile() and member.size <= 10_000_000, "Unexpected manuscript archive entry"
            )
            name = str(path)
            require(name not in files, "Duplicate archive entry")
            files[name] = bundle.extractfile(member).read()
    inventory = json.loads((ROOT / "reproduction/results/paper-source-manifest.json").read_text())
    require(set(files) == set(inventory["files"]), "Manuscript inventory differs")
    metadata = json.loads(files["00README.json"])
    roots = [s["filename"] for s in metadata["sources"] if s["usage"] == "toplevel"]
    require(roots == ["preprint_mlsys.tex"], "Unexpected preprint root")
    # Deliberately specific to this pinned manuscript, not a general TeX engine.
    # preprintflag includes both the main body and appendix. appendixonlyflag is
    # never defined, so neither supplementary-numbering branch is selected.
    require(b"\\def\\preprintflag{1}" in files[roots[0]], "Preprint flag missing")
    require(
        not any(
            b"\\def\\appendixonlyflag" in v
            for k, v in files.items()
            if k in ("preprint_mlsys.tex", "main_mlsys.tex")
        ),
        "Unexpected appendix-only flag",
    )
    visited, floats, anchors = [], [], {}
    counters = Counter()

    def visit(name, stack):
        require(name not in stack and name in files, "Invalid or cyclic input")
        require(name not in visited, "Repeated input requires separate analysis")
        visited.append(name)
        raw = files[name].decode("utf-8")
        text = re.sub(r"(?<!\\)%[^\n]*", "", raw)
        # Comment removal preserves line numbers.
        for label in LABEL.finditer(text):
            key = label.group(1)
            require(key not in anchors, "Duplicate label: " + key)
            anchors[key] = {"path": name, "line": text[: label.start()].count("\n") + 1}
        events = [(m.start(), "input", m) for m in INPUT.finditer(text)]
        events += [(m.start(), "float", m) for m in FLOAT.finditer(text)]
        for _, kind, match in sorted(events, key=lambda e: e[0]):
            if kind == "input":
                child = str(PurePosixPath(match.group(1)))
                if not child.endswith(".tex"):
                    child += ".tex"
                require(".." not in PurePosixPath(child).parts, "Unsafe input")
                visit(child, stack + [name])
                continue
            labels = LABEL.findall(match.group("body"))
            require(labels, "Unlabeled float requires manual review")
            outer = labels[-1]
            category = "table" if match.group("kind").startswith("table") else "figure"
            require(
                outer.startswith("tab:" if category == "table" else "fig:"),
                "Unexpected outer float label",
            )
            counters[category] += 1
            floats.append(
                {
                    "label": outer,
                    "kind": category,
                    "number": counters[category],
                    "path": name,
                    "line": text[: match.start()].count("\n") + 1,
                    "subpanels": labels[:-1],
                }
            )

    visit(roots[0], [])
    require(counters == {"table": 17, "figure": 7}, "Unexpected float inventory")
    require(
        {f["label"] for f in floats} == set(config["floats"]),
        "A float is missing from, or extra in, the interpretation ledger",
    )
    return files, visited, floats, anchors


def annotate(row):
    role = row["role"]
    require(role in ("experiment", "history", "method", "configuration"), "Unknown role")
    row["original_result_reproduced"] = False if role in ("experiment", "history") else None
    row["assessment"] = {
        "experiment": "independent analogue only; original result not reproduced",
        "history": "historical original measurement unavailable",
        "method": "independent restricted implementation; broader coverage remains",
        "configuration": "published setup recorded; independent execution differs",
    }[role]
    return row


def render(report, output):
    def link(path, label=None):
        import os

        return f"[{label or path}]({os.path.relpath(ROOT / path, output)})"

    text = [
        "# Result-by-result paper audit\n",
        "**The original paper is not fully reproduced.** This inventory follows the",
        "arXiv v1 preprint's actual source inputs: **17 tables, seven outer figure",
        "groups and 16 additional narrative anchors**. These overlap; they are not",
        "forty comparable experiments or a denominator for a completion percentage.\n",
        "The source archive and every evidence file below are bound by SHA-256 in",
        "[audit.json](audit.json). Enumeration checks source coverage; the target",
        "interpretations and dependency assessments are authored judgments. This audit",
        "does not rerun Lean, models or GPUs, and file integrity alone does not prove",
        "a study's validity. Follow the linked study records for checks and limits.\n",
        "All seventeen workload shapes have independent full-size contracts (34",
        "HIP/CUDA certificates), with 170 exact-source trials and 19,387,200 scalar",
        "comparisons per MI350X host. The separate shuffle and single-instruction",
        "MFMA studies and completed free local model cohorts are additional evidence.",
        "None supplies the original optimized registry or historical model outcomes.\n",
        "| Paper item / source label | Role and assessment | Available evidence / scope | Missing inputs |",
        "| --- | --- | --- | --- |",
    ]
    for row in report["floats"] + report["narrative"]:
        label = row.get("label", row.get("anchor"))
        title = (f"{row['kind'].title()} {row['number']}: " if "kind" in row else "") + row["title"]
        evidence = ", ".join(
            link(report["evidence_groups"][g][0], g) for g in row["evidence_groups"]
        )
        text.append(
            f"| {title}<br>`{label}` | {row['role']}: {row['assessment']} | "
            f"{row['available_evidence']} {evidence} | "
            + ", ".join(f"`{d}`" for d in row["dependencies"])
            + " |"
        )
    text += ["\n## Concrete dependencies\n"]
    for key, description in report["dependencies"].items():
        text.append(f"- **{key}**: {description}")
    text += [
        "\n## Bounded artifact search\n",
        "The expanded read-only GitHub audit inspected the author's eleven public",
        "repositories and the related AICrossSim organization. At the recorded",
        "revision, `jiaeenie/gpu_optim_bench` identifies itself as FlashInfer-Bench;",
        "its complete 559-entry tree has no LARK/Lean/KernelCraft-named path or",
        "`.lean`, `.ptx` or `.hip` file. This does not exclude hidden material in",
        "other files, other branches, unsearched repositories or a later release.",
        "The related `AICrossSim/KernelCraft` repository was empty at the check.",
        link("reproduction/results/artifact-expanded-20261110.json", "Raw commands and responses")
        + ".\n",
        "The source inventory has 47 manuscript/figure files and no implementation",
        "or original GQA project. No author contact was made. Artifact availability",
        "is an external dependency; broader software support remains implementation",
        "work, and no AMD result can be relabeled as an H100 measurement.\n",
    ]
    return "\n".join(text).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-archive", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--check", action="store_true", help="Compare with an existing audit without rewriting it"
    )
    args = parser.parse_args()
    config_bytes = (HERE / "targets.json").read_bytes()
    config = json.loads(config_bytes)
    files, visited, floats, anchors = manuscript(args.source_archive, config)
    for row in floats:
        row.update(config["floats"][row["label"]])
        annotate(row)
    narrative = []
    for target in config["narrative"]:
        row = dict(target)
        require(row["anchor"] in anchors, "Narrative anchor missing")
        row.update(anchors[row["anchor"]])
        narrative.append(annotate(row))
    evidence = {}
    for row in floats + narrative:
        require(set(row["dependencies"]) <= config["dependencies"].keys(), "Unknown dependency")
        require(
            set(row["evidence_groups"]) <= config["evidence_groups"].keys(),
            "Unknown evidence group",
        )
    for group in config["evidence_groups"].values():
        for path in group:
            p = ROOT / path
            require(
                p.is_file() and p.resolve().is_relative_to(ROOT.resolve()),
                "Invalid evidence: " + path,
            )
            evidence[path] = digest(p.read_bytes())
    report = {
        "schema": 1,
        "paper": config["paper"],
        "scope": config["scope"],
        "original_paper_fully_reproduced": False,
        "completion_percentage": None,
        "evidence_commit": config["evidence_commit"],
        "source_archive_sha256": config["source_archive_sha256"],
        "source_files_sha256": {p: digest(b) for p, b in sorted(files.items())},
        "preprint_input_order": visited,
        "counts": {"tables": 17, "outer_figure_groups": 7, "narrative_anchors": len(narrative)},
        "floats": floats,
        "narrative": narrative,
        "dependencies": config["dependencies"],
        "evidence_groups": config["evidence_groups"],
        "evidence_sha256": dict(sorted(evidence.items())),
        "targets_sha256": digest(config_bytes),
        "auditor_sha256": digest(Path(__file__).read_bytes()),
        "fresh_lean_checks": 0,
        "fresh_gpu_trials": 0,
        "model_calls": 0,
    }
    contents = {"audit.json": encoded(report), "RESULTS.md": render(report, args.output)}
    contents["manifest.json"] = encoded({k: digest(v) for k, v in contents.items()})
    if args.check:
        for name, value in contents.items():
            require((args.output / name).read_bytes() == value, "Audit differs: " + name)
    else:
        require(not args.output.exists(), "Refusing to overwrite an earlier audit")
        args.output.mkdir(parents=True)
        for name, value in contents.items():
            (args.output / name).write_bytes(value)
    print(
        json.dumps(
            {
                "status": "checked" if args.check else "written",
                **report["counts"],
                "evidence_files": len(evidence),
                "original_paper_fully_reproduced": False,
            }
        )
    )


if __name__ == "__main__":
    main()
