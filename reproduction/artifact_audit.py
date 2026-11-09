"""Record a bounded, read-only search for the authors' public reproduction artifacts.

An empty search is evidence about these endpoints, never proof that no release exists.
No messages, issues, emails, or model requests are sent.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.output.exists():
        raise SystemExit("Refusing to overwrite an earlier audit")
    queries = [
        [
            "gh",
            "search",
            "repos",
            '"Lean-Assisted Reasoning"',
            "--limit",
            "100",
            "--json",
            "fullName,description,url",
        ],
        [
            "gh",
            "search",
            "repos",
            "LARK Lean GPU",
            "--limit",
            "100",
            "--json",
            "fullName,description,url",
        ],
        [
            "gh",
            "api",
            "repos/AICrossSim/KernelCraft",
            "--jq",
            "{full_name,size,default_branch,pushed_at,html_url}",
        ],
        ["gh", "api", "repos/AICrossSim/KernelCraft/contents"],
        [
            "gh",
            "api",
            "orgs/AICrossSim/repos",
            "--paginate",
            "--jq",
            '.[] | select((.name|ascii_downcase|contains("lark")) or (.name|ascii_downcase|contains("kernel"))) | {full_name,size,html_url}',
        ],
        [
            "gh",
            "api",
            "users/jiaeenie/repos",
            "--paginate",
            "--jq",
            ".[] | {full_name,description,html_url}",
        ],
    ]
    report = {
        "schema": 1,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "paper": "https://arxiv.org/abs/2611.02028v1",
        "scope": "GitHub repository search, the AICrossSim organization and author jiaeenie. Not an exhaustive search of all authors or private/unindexed/supplemental releases.",
        "queries": [],
        "model_calls": 0,
        "paper_source_inventory": "results/paper-source-manifest.json",
    }
    inventory = Path(__file__).resolve().parent / "results/paper-source-manifest.json"
    report["paper_source_inventory_sha256"] = hashlib.sha256(inventory.read_bytes()).hexdigest()
    for command in queries:
        response = subprocess.run(command, text=True, capture_output=True, timeout=60)
        report["queries"].append(
            {
                "command": command,
                "exit_code": response.returncode,
                "stdout": response.stdout,
                "stderr": response.stderr,
            }
        )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
