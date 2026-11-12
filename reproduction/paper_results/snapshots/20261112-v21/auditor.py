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


def check_new_production_evidence(config, production_cases):
    """Check claim consistency; the linked study checks establish proof validity."""
    checks = config["production_proof_checks"]
    require(set(checks) == {"flashinfer-rmsnorm", "sglang-rmsnorm", "vllm-awq-gemm"},
            "New production proof inventory differs")
    outcomes = {}
    for case, expected in checks.items():
        row = next(r for r in production_cases if r["paper_case"] == case)
        report_path = ROOT / expected["report"]
        replay_path = ROOT / expected["replay"]
        report = json.loads(report_path.read_text())
        replay = json.loads(replay_path.read_text())
        require(row["independent_status"] == "complete-scoped-proof"
                and type(row["registered_source_certificates"]) is int
                and row["registered_source_certificates"] == 4, "New production certificate count differs")
        for record in (report, replay):
            require(type(record["source_certificates"]) is int and record["source_certificates"] == 4
                    and record["whole_kernel_execution_proved"] is True
                    and record["actual_trace_race_freedom_proved"] is True
                    and record["source_reference_equality_proved"] is True
                    and record["ieee_equivalence_proved"] is False
                    and record["floating_point_error_bound_proved"] is False
                    and record["original_paper_fully_reproduced"] is False
                    and type(record["model_calls"]) is int and record["model_calls"] == 0
                    and type(record["gpu_trials"]) is int and record["gpu_trials"] == 0,
                    "New production proof scope differs: " + case)
        require(report["model_profile"] == expected["profile"]
                and report["local_lean_modules"] == replay["local_lean_modules"] == expected["modules"]
                and replay["axiom_audits"] == expected["audit_occurrences"]
                and replay["false_lean_claims_rejected"] == report["false_lean_claims_rejected"]
                    == expected["false_lean_claims"]
                and replay["git_available_on_replay_path"] is False
                and replay["own_lean_compiled_cache_seeded"] is False,
                "New production replay scope differs: " + case)
        archive = report_path.parent / "source.tar.gz"
        require(report["source_archive_sha256"] == replay["source_archive_sha256"] == digest(archive.read_bytes()),
                "New production archive binding differs: " + case)
        require(expected["audit_occurrences"] == len(report["library_axiom_audits"])
                + 4*len(report["main_axiom_audits"]), "New production audit count differs: " + case)
        outcomes[case] = {
            "model_profile": expected["profile"], "source_certificates": 4,
            "whole_launch_race_freedom_and_dense_real_equality": True,
            "owned_lean_modules": expected["modules"], "axiom_audit_occurrences": expected["audit_occurrences"],
            "source_and_replay_metadata_consistent": True, "fresh_lean_check_performed_by_this_audit": False,
        }
    return outcomes


def render(report, output):
    def link(path, label=None):
        return f"[{label or path}]({report['evidence_links'][path]})"

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
        "The later upstream-derived SiLU study supplies eight native multiwave",
        "HIP/CUDA certificates for one independently adapted family. The exact-real",
        "wave64 reduction study supplies one further primitive, with 17,408 source-tree",
        "bit comparisons per host and cancellation disagreements reported separately.",
        "The independent native weighted RMSNorm study adds four source-bound",
        "canonical-real certificates and fresh rechecks at 1, 3, 64 and 255 rows.",
        "Its whole-launch proof covers all inputs/outside memory for 1<=rows<256",
        "at width16384, native block1024/wave64, including logical-16 shuffles.",
        "Earlier both-host measurements add 127,008,768 CPU-reference comparisons",
        "with zero tolerance failures; signed-zero and one-half-ULP differences",
        "remain explicit. No IEEE error theorem or complete upstream API is claimed.",
        "The independent native online-attention study adds full actual-launch",
        "execution, actual-trace race freedom and dense-real correctness for all",
        "groups 1..65535 at N128/D256, block32/wave64. It proves every output after",
        "all four key tiles, nine block phases and final PC90 halt, preserving the",
        "source's arithmetic order and half-cast sites in its abstract-operator theorem.",
        "Four canonical-real exports and two fresh standalone archive replays pass.",
        "The real interpretation makes casts identities; IEEE equivalence and a",
        "floating-point error bound remain unproved. Earlier paired AMD measurements",
        "supply 3,145,728 CPU-double comparisons with zero tolerance failures; measured",
        "FP16-versus-rounded-FP32 differences remain explicit. This ledger adds no",
        "GPU trials, model calls or Lean checks of its own.",
        "The complete independent fused add RMSNorm study adds four canonical-real",
        "exports for seeded in-place buffers and both outputs, with fresh standalone",
        "replay. Paired AMD audits retain 127,008,768 normalized comparisons and",
        "equally many residual-bit comparisons, with no tolerance/bit failures.",
        "The independent llm.c HIP softmax repair now has complete-grid execution,",
        "actual-trace race freedom and dense-real correctness at width50257 for",
        "rows1..42730. Both original and repaired full programs are source-bound.",
        "The original source's conflicting accesses are proved members of an actual",
        "complete block trace reached from initialization; a supported one-row",
        "original launch is racy and fails Correct for every reference. This does",
        "not assert generic original multirow completion or equality to synthetic",
        "whole-State snippets. Fresh source/replay each check 134 modules, 1,530",
        "audits and 11 false claims; 48 rehashed metadata guards reject scope changes.",
        "The earlier softmax checkpoint records eight passed CI jobs, including 160",
        "ordinary tests with nine optional skips.",
        "Paired AMD softmax measurements add 2,036,413,640 value comparisons with",
        "zero tolerance failures. Its development reader issues zero registered",
        "softmax source certificates. The separate canonical-real packet is idealized.",
        "The paper excludes IEEE/rounding guarantees from its formal scope and",
        "tests floating-point behavior numerically. IEEE/error-bound theorems are",
        "therefore scope limits here, not unreproduced paper results.",
        "Both native rotary-embedding layouts now have complete actual-launch",
        "correctness and race-freedom proofs, extraction of both seeded Q/K buffers",
        "and eight source-bound certificates. Their independent dense formula fixes",
        "source-order scalar operations and explicit half casts; the proof needs Std.",
        "Both native fused QK normalization/RoPE layouts now have complete actual",
        "launch proofs, race freedom, output extraction and equality to independent",
        "exact-real dense references. Four interleaved v20 and four split-half v21",
        "certificates are published. Split-half source/replay check 69 owned modules,",
        "582 axiom sets, four specializations and twelve false Lean claims; eight",
        "rehashed scope controls are refused before extraction. Both layouts replay",
        "without Git or seeded owned proof caches; installed wheels and anonymous",
        "public downloads are checked. That earlier fused rotary checkpoint records",
        "twelve passed CI jobs.",
        "Each rotary study separately retains 79,626,240 CPU-reference comparisons",
        "across both AMD hosts, with zero tolerance failures and zero adapted/upstream",
        "word differences. Fused QK has 3,948 FP16-word differences from rounded Torch",
        "FP32, within the stated tolerance. These measurements are not IEEE theorems.",
        "Nine accepted production families and the rejected original softmax race",
        "case now have independent scoped coverage. The distinct FlashInfer RMSNorm",
        "profile proves full native logical32/block1024 execution, actual-trace race",
        "freedom and dense exact-real equality for rows1..131072 at width16384.",
        "Four exports and rechecks pass; its frozen replay checks 68 owned modules,",
        "522 axiom-audit occurrences and eight false Lean claims. Paired AMD results",
        "retain 127,008,768 CPU float64 comparisons with zero tolerance failures.",
        "Guarded SGLang packed RMSNorm also proves full native execution, actual",
        "whole-trace race freedom and dense-real equality for rows1..131072 at",
        "width16384, retaining both reductions/barriers and three private half[16]",
        "caches. Four exports/rechecks and frozen replay pass 782 axiom audits over 88",
        "owned modules and eighteen false Lean claims. The lane-zero partial-store",
        "repair is explicit; the selected unguarded adaptation's reached conflicting",
        "writes remain separate. Its paired AMD packet retains 190,513,152 CPU",
        "float64 comparisons with zero tolerance failures and recorded FP32 differences.",
        "Native FP16 single-split-K AWQ GEMM proves the complete initialized launch,",
        "actual whole-trace race freedom, every output and dense exact-real matrix",
        "product equality for all supported positive M,K,N with K%32=0,N%64=0 and",
        "signed address bounds. Both native MFMA K16 passes, all K32 iterations,",
        "guarded converted stores and original fuel remain. Four exports and rechecks",
        "pass; independent source-only replay checks 83 owned modules, 734 axiom-audit",
        "occurrences and fourteen false Lean claims. Another 38 rehashed scope changes",
        "fail before extraction. Paired AMD results retain 820,224 CPU float64",
        "comparisons over 120 launches with zero tolerance failures or host bit",
        "differences; 380 FP16-word differences from rounded CPU Torch FP32 are recorded.",
        "These three new profiles also pass installed-wheel and anonymous public",
        "source-download/binding checks. Their real interpretations make half casts",
        "identities; IEEE equality/error bounds are outside the formal claim.",
        "CI receipts are tied to their exact source commits and observation times.",
        "The AWQ publication receipt recorded its new 18-job run in progress; older",
        "passed checkpoints are not a completion claim for that new source run.",
        "The paper removes AWQ int4 dequantization. The independent AMD adaptation",
        "retains FP16 weights and one split-K iteration, while its physical wave64",
        "MFMA fragments differ from the authors' adapted NVIDIA PTX.",
        "None supplies the original optimized registry or historical model outcomes.\n",
        f"This snapshot freezes selected evidence from published-evidence commit `{report['evidence_commit'][:7]}`",
        "and the recorded release/CI responses. Its replay reads that frozen bundle,",
        "so later repository documentation changes do not invalidate this audit.",
        "Evidence links for existing studies point to that exact Git commit.\n",
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
    text += [
        "\n## Ten production cases\n",
        "The case names and order below are checked against the manuscript table.",
        "Statuses are authored assessments of independent scoped evidence; none",
        "reproduces an original model/token-cost result. Certificate counts belong",
        "to separate fixed profiles, not a count of original paper certificates.\n",
        "| Paper case | Independent coverage | Registered exports | Scope |",
        "| --- | --- | --- | --- |",
    ]
    for row in report["production_cases"]:
        links = ", ".join(
            link(report["evidence_groups"][g][0], g) for g in row["evidence_groups"]
        )
        text.append(
            f"| `{row['paper_case']}` | {row['independent_status']} | "
            f"{row['registered_source_certificates']} | {row['scope']} {links} |"
        )
    text += ["\n## Concrete dependencies\n"]
    for key, description in report["dependencies"].items():
        kind = report["dependency_kinds"][key]
        text.append(f"- **{key}** ({kind}): {description}")
    text += [
        "\n## Bounded artifact search\n",
        "The earlier audit inspected eleven public repositories of author Jiayi Nie",
        "and the related AICrossSim organization. A later recorded check finds the",
        "KernelCraft repository still empty and the benchmark repository unchanged.",
        "A profile matching the lead author's name and earlier publication repositories",
        "has eight public repositories; this attribution is an inference. The pinned",
        "DeepFusionKernel tree has 1,519 entries and no Lean/LARK/KernelCraft paths.",
        "Its only matched .hip path is a bundled SGLang all-reduce header; its README",
        "describes the separate Deep Kernel Fusion for Transformers project.",
        "Repository searches are bounded, including a 100-result limit in one query.",
        "These observations do not exclude private, unindexed, other-author or",
        "other-branch releases, or artifacts embedded under unsearched file names.",
        link("reproduction/results/artifact-expanded-20261110.json", "Earlier raw records")
        + "; "
        + link(
            "reproduction/paper_results/snapshots/20261110-v16/artifact-release-recheck.json",
            "release recheck",
        )
        + "; "
        + link(
            "reproduction/paper_results/snapshots/20261110-v16/lead-author-gpu-tree.json",
            "pinned candidate-author tree",
        )
        + ".\n",
        "A fresh bounded check again finds only v1 on the abstract page, no dedicated",
        "implementation link in the inspected author publication entry, eleven public",
        "repositories on that author account, an empty KernelCraft repository and the",
        "same previously inspected benchmark commit. Exact repository-title/arXiv",
        "searches returned no matching repository; search coverage is limited.",
        link("reproduction/paper_results/snapshots/20261110-v17/release-refresh.json", "Fresh bounded records") + ".\n",
        "Additional bounded GitHub code/commit searches found a third-party arXiv",
        "announcement and unrelated game-data paths, with no original implementation",
        "located. Exact-token searches can miss renamed, private or unindexed code.",
        link("reproduction/paper_results/snapshots/20261110-v18/artifact-code-search.json",
             "Code/commit search records") + ".\n",
        "The later November11 bounded check again found KernelCraft empty and the",
        "inspected benchmark head unchanged, with arXiv still at v1 and no visible",
        "code link in the inspected publication entry. Private, unindexed, other",
        "branches/accounts and future releases remain outside this bounded search.",
        link("reproduction/production_softmax/results/exp-wave-artifact-recheck-v1/results.json",
             "November11 bounded records") + ".\n",
        "A further November12 bounded primary-page/API check again finds only arXiv",
        "v1, an empty KernelCraft repository, the inspected benchmark head unchanged,",
        "and an arXiv-only LARK publication entry on the inspected coauthor page.",
        "The exact-title repository search returns this independent reproduction.",
        "Three additional candidate READMEs describe separate projects, including",
        "a deterministic-inference project that cites LARK as related work.",
        "The broader repository query returns 256 results and inspects only its first 30;",
        "this bounded check does not establish absence from other results or sources.",
        link("reproduction/paper_results/original-artifact-refresh-20261112-v21/results.json",
             "November12 bounded observations") + ".\n",
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
    production_cases = config["production_cases"]
    paper_cases = re.findall(
        r"\\multicolumn\{1\}\{m\{2cm\}\}\{([^}]+)\}",
        files["tables/lib_veri.tex"].decode("utf-8"),
    )
    require(
        len(paper_cases) == 10
        and paper_cases == [row["paper_case"] for row in production_cases],
        "Production case inventory differs from manuscript",
    )
    for row in production_cases:
        require(row["original_result_reproduced"] is False,
                "Unsupported original production result")
        require(set(row["evidence_groups"]) <= config["evidence_groups"].keys(),
                "Unknown production evidence group")
    require(sum(row["independent_status"] == "complete-scoped-proof" for row in production_cases) == 9
            and sum(row["registered_source_certificates"] for row in production_cases) == 48,
            "Independent production inventory differs")
    production_checks = check_new_production_evidence(config, production_cases)
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
        "production_cases": production_cases,
        "production_evidence_checks": production_checks,
        "dependencies": config["dependencies"],
        "evidence_groups": config["evidence_groups"],
        "evidence_links": config["evidence_links"],
        "dependency_kinds": config["dependency_kinds"],
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
