"""Replay refused model candidates after removing comments only; no model calls.

This is a separately labeled harness-sensitivity experiment. It never changes
raw responses, original request histories, or the matched cohort's counts.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.local_models import client
from reproduction.local_models.compare_models import COHORTS, REPO, RESULTS, audit_cohort


def remove_comments(source):
    """Mask Lean comments while preserving newlines, columns and all other code.

    This limited replay refuses quoted strings/names/character syntax outside
    comments rather than guessing whether a marker belongs to a literal.
    Nested block comments and line comments are recognized explicitly.
    """
    if not isinstance(source, str) or len(source) > 20000:
        raise ValueError("Expected a bounded proof string")
    if "\r" in source.replace("\r\n", ""):
        raise ValueError("Isolated carriage returns are outside this replay")
    output, i, depth, removed = list(source), 0, 0, 0

    def mask(start, end):
        for j in range(start, end):
            if source[j] not in "\r\n":
                if ord(source[j]) > 127 or source[j] == "\t":
                    raise ValueError("Only ASCII comment text without tabs is replayed")
                output[j] = " "

    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                removed += 1
                mask(i, i + 2)
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                mask(i, i + 2)
                i += 2
            else:
                mask(i, i + 1)
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            mask(i, end)
            removed += 1
            i = end
        elif source.startswith("/-", i):
            if source.startswith(("/--", "/-!"), i):
                raise ValueError("Documentation comments are tokens, not replayable whitespace")
            depth = 1
            removed += 1
            mask(i, i + 2)
            i += 2
        else:
            if source[i] in {'"', "«", "»"} or (
                source[i] == "'"
                and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'"))
            ):
                raise ValueError("Quoted forms are outside this comments-only replay")
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(output), removed


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", choices=sorted(COHORTS), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("fresh output directory required")
    runs = [RESULTS / r for r in COHORTS[args.model]["runs"]]
    # Establish the unchanged baseline, including response authorship and a
    # fresh check of each original successful certificate, before any replay.
    baseline, logs = audit_cohort(args.model, runs, lean=args.lean)
    args.output.mkdir(parents=True)
    for name, log in logs.items():
        target = args.output / "baseline-rechecks" / (name + ".log")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(log)
    result = {
        "schema": 1,
        "status": "running",
        "model": baseline["model"],
        "baseline": baseline,
        "model_calls_in_replay": 0,
        "external_api_spend_usd": 0,
        "original_cohort_results_changed": False,
        "original_paper_fully_reproduced": False,
        "normalization": "Mask recognized line/nested block comments with whitespace; preserve all other code and the original segmentation. Refuse unsupported quoted forms; keep the original proof-policy validator and axiom audit.",
        "runner_sha256": sha(Path(__file__)),
        "baseline_auditor_sha256": sha(Path(__file__).with_name("compare_models.py")),
        "certificate_code_sha256": sha(Path(certificate.__file__)),
        "candidates": [],
    }
    for root in runs:
        report = json.loads((root / "results.json").read_text())
        for i, case in enumerate(report["cases"]):
            for call in case["calls"]:
                if call["status"] != "invalid-proposal":
                    continue
                attempt = root / f"case-{i:02d}" / f"attempt-{call['attempt']:02d}"
                response = json.loads((attempt / "response.json").read_text())
                content = response["choices"][0]["message"].get("content")
                try:
                    original = client.proposal(content)
                except (ValueError, TypeError, AttributeError):
                    continue
                proofs = original.get("proofs")
                if not isinstance(proofs, dict) or set(proofs) != set(certificate.DEFAULT_PROOFS):
                    continue
                if not all(isinstance(p, str) for p in proofs.values()):
                    continue
                if not any("--" in p or "/-" in p for p in proofs.values()):
                    continue
                dest = args.output / f"candidate-{len(result['candidates']):02d}"
                dest.mkdir()
                write(dest / "original-proposal.json", original)
                normalized = deepcopy(original)
                row = {
                    "case": case["case"],
                    "original_attempt": call["attempt"],
                    "original_outcome": call["status"],
                    "source_run": str(root.relative_to(RESULTS)),
                    "source_attempt": str(attempt.relative_to(root)),
                    "request_sha256": sha(attempt / "request.json"),
                    "response_sha256": sha(attempt / "response.json"),
                    "original_proposal_sha256": sha(dest / "original-proposal.json"),
                    "artifacts": dest.name,
                    "comments_removed_by_slot": {},
                    "actual_lean_check": False,
                }
                try:
                    for name, proof in proofs.items():
                        text, n = remove_comments(proof)
                        normalized["proofs"][name] = text
                        row["comments_removed_by_slot"][name] = n
                    certificate.validate_proofs(normalized["proofs"])
                    write(dest / "normalized-proposal.json", normalized)
                    fixture = REPO / case["case"]
                    checked = certificate.verify(
                        fixture / "kernel.hip",
                        fixture / "reference.py",
                        fixture / "task.json",
                        dest / "certificate",
                        lean=args.lean,
                        timeout=150,
                        proposal_path=dest / "normalized-proposal.json",
                    )
                    row["actual_lean_check"] = True
                    row["status"] = (
                        "unproved"
                        if checked["status"] != "verified"
                        else "verified-normalized-candidate"
                    )
                    row["lean_timeout"] = "Lean timed out" in checked["axiom_audit"]
                    if checked["status"] == "verified":
                        log = certificate.check(dest / "certificate", lean=args.lean, timeout=150)
                        (dest / "independent-recheck.log").write_text(log)
                        row["independent_recheck"] = "verified"
                except (ValueError, OSError, KeyError, TypeError) as error:
                    row.update(status="replay-refused-or-error", error=str(error))
                result["candidates"].append(row)
                write(args.output / "results.json", result)
                print(Path(case["case"]).name, call["attempt"], row["status"], flush=True)
    result.update(
        status="finished",
        comment_candidates=len(result["candidates"]),
        actual_lean_replay_checks=sum(c["actual_lean_check"] for c in result["candidates"]),
        normalized_candidates_verified_and_rechecked=sum(
            c.get("independent_recheck") == "verified" for c in result["candidates"]
        ),
        scope="Separately replayed observed candidates under a comments-only transformation. These are not raw accepted model responses, a new interactive cohort, counterfactual token costs, the matched comparison's pass rates, or original-paper ablations. Raw artifacts and baseline counts remain unchanged.",
    )
    write(args.output / "results.json", result)
    write(
        args.output / "manifest.json",
        {
            str(p.relative_to(args.output)): sha(p)
            for p in sorted(args.output.rglob("*"))
            if p.is_file() and p != args.output / "manifest.json"
        },
    )


if __name__ == "__main__":
    main()
