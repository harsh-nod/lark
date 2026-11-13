"""Check the displayed Level-2 token averages against the pinned manuscript.

This checks arithmetic in the published table, not the underlying experiments.
It neither repairs manuscript numbers nor reconstructs original model histories.
"""

import argparse
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_UP
import hashlib
import json
from pathlib import Path
import re
import tarfile

ARCHIVE_SHA256 = "095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2"
MEMBER = "tables/opus_veri.tex"
MEMBER_SHA256 = "3d5135a796af430e059f8e4ff8acb99fdd967d0867aa9e7c5ca2512eb506a6b5"
TASKS = ["ffn", "swiglu", "rope", "flash_attention", "gqa"]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def rounded(value):
    return str(value.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def audit(source_archive):
    require(digest(source_archive.read_bytes()) == ARCHIVE_SHA256,
            "Pinned original manuscript archive required")
    with tarfile.open(source_archive) as archive:
        content = archive.extractfile(MEMBER).read()
    require(digest(content) == MEMBER_SHA256, "Pinned Level-2 table member required")
    source = content.decode()
    require("failed or stopped at their budget and left out of the Total average" in source,
            "The caption's stated exclusion rule differs")
    blocks = re.findall(r"\\multirow\{3\}\{\*\}\{([^}]+)\}(.*?)(?=\\midrule|\\bottomrule)",
                        source, re.S)
    require([name for name, _ in blocks] == ["Opus 5.5", "GLM 5.3"],
            "Expected both Level-2 models exactly once")
    rows = []
    for model, block in blocks:
        passes = re.findall(r"& pass & (.*?) \\\\", block)
        require(len(passes) == 1, "Unique pass row required")
        statuses = [value.strip() for value in passes[0].split("&")[:-1]]
        require(len(statuses) == 5 and set(statuses) <= {r"\cmark", r"\xmark"},
                "Expected five task outcomes")
        verified = [value == r"\cmark" for value in statuses]
        metrics = re.findall(r"& (input|output) token \(M\) & (.*?) \\\\", block)
        require([name for name, _ in metrics] == ["input", "output"],
                "Expected both token-cost rows")
        for metric, line in metrics:
            columns = [value.strip() for value in line.split("&")]
            require(len(columns) == 6, "Expected five task values and their displayed total")
            values = [Decimal(value.strip("()")) for value in columns[:-1]]
            require(all((value.startswith("(") and value.endswith(")")) is (not ok)
                        for value, ok in zip(columns[:-1], verified)),
                    "Failure parentheses and task outcomes disagree")
            accepted = [value for value, ok in zip(values, verified) if ok]
            require(accepted, "This table's success-only mean needs a successful task")
            success_mean = sum(accepted) / len(accepted)
            all_mean = sum(values) / len(values)
            displayed = Decimal(columns[-1])
            rows.append({
                "model": model, "metric": metric, "unit": "millions of tokens",
                "tasks": [{"task": task, "verified": ok, "cost_M": str(value)}
                          for task, ok, value in zip(TASKS, verified, values)],
                "successful_tasks": len(accepted), "all_tasks": len(values),
                "displayed_total_M": str(displayed),
                "success_only_mean_M": str(success_mean),
                "success_only_mean_rounded_M": rounded(success_mean),
                "all_task_mean_M": str(all_mean),
                "all_task_mean_rounded_M": rounded(all_mean),
                "displayed_matches_caption_rule_at_reported_precision":
                    displayed == Decimal(rounded(success_mean)),
                "displayed_matches_all_task_mean_at_reported_precision":
                    displayed == Decimal(rounded(all_mean)),
            })
    return {
        "schema": 1, "status": "pinned-Level-2-table-arithmetic-checked",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_archive_sha256": ARCHIVE_SHA256,
        "member": MEMBER, "member_sha256": MEMBER_SHA256,
        "paper_label": "tab:verify-model", "caption_rule": "exclude failed/stopped tasks",
        "scope": "Arithmetic of the displayed rounded table cells only; no original logs or "
                 "unrounded costs were available. Both reported GLM totals match the all-task "
                 "means at the displayed precision and disagree with the stated success-only "
                 "rule. This does not identify which values or caption the authors intended.",
        "rows": rows,
        "caption_mismatches": sum(not r["displayed_matches_caption_rule_at_reported_precision"]
                                   for r in rows),
        "driver_sha256": digest(Path(__file__).read_bytes()),
        "model_calls": 0, "lean_checks": 0, "gpu_trials": 0,
        "original_paper_fully_reproduced": False,
    }


def markdown(report):
    lines = ["# Published Level-2 cost-table arithmetic", "", report["scope"], "",
             "| Model | Tokens | Displayed total M | Successful-task mean M | All-task mean M |",
             "| --- | --- | ---: | ---: | ---: |"]
    for row in report["rows"]:
        lines.append(f"| {row['model']} | {row['metric']} | {row['displayed_total_M']} | "
                     f"{row['success_only_mean_rounded_M']} | {row['all_task_mean_rounded_M']} |")
    lines += ["", "The independent full-size cohort comparison follows the caption's "
              "successful-task definition and retains failed-run spending in separate all-task "
              "totals. Its values are not the original model histories.", "",
              "The report binds arXiv:2611.02028v1 and `tables/opus_veri.tex` by SHA-256. "
              "No experiment was rerun and no manuscript value was changed.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-archive", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "Fresh output required")
    report = audit(args.source_archive)
    args.output.mkdir(parents=True)
    write(args.output / "results.json", report)
    (args.output / "RESULTS.md").write_text(markdown(report))
    (args.output / "driver.py").write_bytes(Path(__file__).read_bytes())
    write(args.output / "manifest.json", {p.name: digest(p.read_bytes())
                                         for p in sorted(args.output.iterdir()) if p.is_file()})
    print(json.dumps({"status": report["status"], "rows": len(report["rows"]),
                      "caption_mismatches": report["caption_mismatches"]}))


if __name__ == "__main__":
    main()
