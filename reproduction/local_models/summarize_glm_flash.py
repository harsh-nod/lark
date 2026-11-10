"""Audit completed Flash pilots and their matched first-request budget variant."""

import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from reproduction.local_models.analyze_run import analyze

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/pilot-glm-flash-low-20261109"
RUNS = [
    OUT / "pilot-low-remote-8ad91bc",
    ROOT / "results/pilot-glm-flash-budget4096-20261109/glm-flash-budget4096-remote",
]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    audits = [analyze(r) for r in RUNS]
    reports = [json.loads((r / "results.json").read_text()) for r in RUNS]
    assert audits[0]["model"] == audits[1]["model"] == "zai-org/GLM-5.3-Flash"
    assert audits[0]["revision"] == audits[1]["revision"]
    assert audits[0]["requests"] == 9 and audits[1]["requests"] == 3
    assert reports[0]["server_record_sha256"] == reports[1]["server_record_sha256"]
    rows = []
    for i, name in enumerate(("relu", "silu", "softmax")):
        paths = [r / f"case-{i:02d}/attempt-01" for r in RUNS]
        requests = [json.loads((p / "request.json").read_text()) for p in paths]
        assert requests[1].pop("thinking_token_budget") == 4096
        assert requests[0] == requests[1]
        responses = [json.loads((p / "response.json").read_text()) for p in paths]
        rows.append(
            {
                "case": name,
                "same_request_except_thinking_budget": True,
                "request_hashes": [sha(p / "request.json") for p in paths],
                "first_call_outcomes": [r["cases"][i]["calls"][0]["status"] for r in reports],
                "first_call_usage": [r["usage"] for r in responses],
            }
        )
    summary = {
        "schema": 1,
        "status": "audited-matched-first-request-budget-variant",
        "model": audits[0]["model"],
        "revision": audits[0]["revision"],
        "pairs": rows,
        "unbounded_pilot": {k: v for k, v in audits[0].items() if k != "files"},
        "budgeted_pilot": {k: v for k, v in audits[1].items() if k != "files"},
        "external_api_spend_usd": 0,
        "scope": "Three matched first requests; only thinking_token_budget differs. Independent reduced fixtures/proof slots, not original agent ablation. Retry counts differ between full runs (3 versus 1 per case). Runtime/cache/batching and statistical variation were not controlled.",
    }
    (OUT / "budget-comparison.json").write_text(json.dumps(summary, indent=2) + "\n")
    table = [
        f"| {r['case']} | {r['first_call_outcomes'][0]} | {r['first_call_outcomes'][1]} | {r['first_call_usage'][0]['completion_tokens']:,} / {r['first_call_usage'][1]['completion_tokens']:,} |"
        for r in rows
    ]
    (ROOT / "GLM_FLASH_RESULTS.md").write_text(
        """# Independent GLM-5.3-Flash proof pilots

Run date: 2026-11-09. **No original-paper pass-rate claim.**
[Baseline receipts](results/pilot-glm-flash-low-20261109/),
[reasoning-budget variant](results/pilot-glm-flash-budget4096-20261109/),
[matched-request audit](results/pilot-glm-flash-low-20261109/budget-comparison.json).

The low-effort baseline completed nine requests across three reduced HIP fixtures:
**eight reasoning-only responses, one unproved Lean check, zero certificates**.
Reported usage was 84,888 prompt + 146,704 completion = **231,592 total tokens**.
This replaces the earlier in-progress status without discarding the interrupted
600-second/max-effort/SSH-forward failure records.

A separate 4,096-reasoning-token variant made one request per fixture, returning
one unproved Lean candidate and two invalid proposals. It used **50,976 reported
tokens** and verified no certificates. Invalid proposals are not Lean rejections.
Hosted API spending was **$0** in both runs; GPU time/electricity are not priced.

## Matched first requests

For each fixture the entire decoded request, including messages, model, seed,
temperature, output cap and reasoning effort, matches after removing the added
`thinking_token_budget:4096` field. Both runs used the same checkpoint, image
and ready runtime record. Compare only the first request in this table: later
baseline retries have different feedback and no matching variant retry.

| Reduced fixture | Baseline first outcome | Budgeted first outcome | Completion tokens: baseline / budgeted |
| --- | --- | --- | ---: |
"""
        + "\n".join(table)
        + """

The budgeted requests returned final proposal content in these three cases;
none yielded a verified certificate. This is a small protocol/budget experiment,
not a statistical performance result or the authors' segmentation/failure-analysis
ablation. The original registry, tools, agent loop and stage costs are absent.
An uncertified attempt does not establish that the kernel is faulty.

An additional disjoint 14-fixture, single-request study is running on a separate
owned runtime with the same checkpoint/image/TP and budget, to complete the
17-fixture first-attempt comparison. It is not included in these completed counts.
`summarize_glm_flash.py` audits receipts and exact paired-request equality before
regenerating this report.
"""
    )
    (OUT / "manifest.json").write_text(
        json.dumps(
            {
                str(p.relative_to(OUT)): sha(p)
                for p in sorted(OUT.rglob("*"))
                if p.is_file() and p.name != "manifest.json"
            },
            indent=2,
        )
        + "\n"
    )
    print(
        "Flash baseline/variant audited; all three first requests match except the reasoning budget"
    )


if __name__ == "__main__":
    main()
