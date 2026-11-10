"""Audit the 3+14-case DeepSeek cohort and independently recheck every model success."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from reproduction.local_models import client
from reproduction.local_models.analyze_run import analyze

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
OUT = ROOT / "results/pilot-deepseek-expanded-20261109"
RUNS = [
    ROOT / "results/pilot-deepseek-budget4096-20261109/deepseek-budget4096-remote",
    OUT / "deepseek-budget4096-additional14-remote",
]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    import argparse

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    reports = [json.loads((r / "results.json").read_text()) for r in RUNS]
    audits = [analyze(r) for r in RUNS]
    for key in (
        "model",
        "server_record_sha256",
        "runner_sha256",
        "client_sha256",
        "seed",
        "temperature",
        "max_tokens",
        "thinking_token_budget",
        "attempts_per_case",
    ):
        assert reports[0][key] == reports[1][key], key
    assert reports[0]["model"] == "deepseek-ai/DeepSeek-V4.1-Flash-1017"
    assert reports[0]["thinking_token_budget"] == 4096 and reports[0]["attempts_per_case"] == 3
    cases, verified = [], []
    for root, report in zip(RUNS, reports):
        for i, case in enumerate(report["cases"]):
            fixture = REPO / case["case"]
            for key, name in (
                ("source_sha256", "kernel.hip"),
                ("reference_sha256", "reference.py"),
                ("task_sha256", "task.json"),
            ):
                assert sha(fixture / name) == case[key]
            cases.append(
                {"case": case["case"], "outcome": case["status"], "requests": len(case["calls"])}
            )
            if case["status"] != "verified":
                continue
            base = root / f"case-{i:02d}"
            last = case["calls"][-1]
            assert last["status"] == "proved"
            attempt = base / f"attempt-{last['attempt']:02d}"
            response = json.loads((attempt / "response.json").read_text())
            proposal = client.proposal(response["choices"][0]["message"]["content"])
            assert (
                proposal
                == json.loads((attempt / "proposal.json").read_text())
                == json.loads((base / "certificate/proposal.json").read_text())
            )
            for n, source in (
                ("kernel.cu", "kernel.hip"),
                ("reference.py", "reference.py"),
                ("task.json", "task.json"),
            ):
                assert (base / "certificate" / n).read_bytes() == (fixture / source).read_bytes()
            log = certificate.check(base / "certificate", lean=args.lean, timeout=150)
            logs = OUT / "independent-rechecks"
            logs.mkdir(exist_ok=True)
            target = logs / (fixture.name + ".log")
            target.write_text(log)
            verified.append(
                {
                    "case": case["case"],
                    "certificate": str((base / "certificate").relative_to(ROOT)),
                    "model_response_matches_exported_proposal": True,
                    "independently_rechecked": True,
                    "recheck_log_sha256": sha(target),
                }
            )
    expected = {
        str(p.relative_to(REPO))
        for p in (REPO / "reproduction/nonlinear/cases/float16").iterdir()
        if (p / "task.json").is_file()
    }
    assert len(cases) == len(expected) == 17 and {c["case"] for c in cases} == expected
    call_counts = Counter()
    for audit in audits:
        call_counts.update(audit["call_outcomes"])
    summary = {
        "schema": 1,
        "status": "audited-independent-17-case-cohort",
        "model": reports[0]["model"],
        "revision": audits[0]["revision"],
        "cases": sorted(cases, key=lambda c: c["case"]),
        "case_outcomes": dict(Counter(c["outcome"] for c in cases)),
        "verified_certificates": verified,
        "call_outcomes": dict(call_counts),
        "requests": sum(a["requests"] for a in audits),
        "responses": sum(a["responses"] for a in audits),
        "lean_checks": sum(a["lean_checks"] for a in audits),
        "usage_incomplete": any(a["usage_incomplete"] for a in audits),
        "reported_usage": {
            k: sum(a["reported_usage"][k] for a in audits)
            for k in ("prompt_tokens", "completion_tokens", "total_tokens")
        },
        "reported_reasoning_tokens": sum(a["reported_reasoning_tokens"] for a in audits),
        "attempts_per_case": 3,
        "max_tokens": 16384,
        "thinking_token_budget": 4096,
        "seed": reports[0]["seed"],
        "temperature": reports[0]["temperature"],
        "external_api_spend_usd": 0,
        "source_runs": [str(r.relative_to(ROOT)) for r in RUNS],
        "scope": "Independent reduced HIP fixtures and immutable three-proof-slot harness; two disjoint case batches with matching settings. Not original registry/kernels, forty-check agent harness, endpoints, failure diagnosis, pass rates or stage costs. Unproved is not a kernel-bug verdict.",
    }
    (OUT / "cohort-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    rows = [
        f"| {Path(c['case']).name} | {c['requests']} | {c['outcome']} |"
        for c in sorted(cases, key=lambda c: c["case"])
    ]
    (ROOT / "DEEPSEEK_RESULTS.md").write_text(
        f"""# Independent DeepSeek proof-proposal cohort

Run date: 2026-11-09. **This is not the paper's original model experiment.**
[Audited summary](results/pilot-deepseek-expanded-20261109/cohort-summary.json),
[three-case batch](results/pilot-deepseek-budget4096-20261109/),
[fourteen-case batch](results/pilot-deepseek-expanded-20261109/).

**{len(verified)} of 17 reduced HIP fixtures verified within three requests per case.**
The successful reduced depthwise-convolution proposal passed the proof-slot
validator, Lean, a fresh certificate export and independent rechecks on the GPU
host and the primary workspace. Its exported tactics match the model's actual
final response; kernel/reference/task bytes match the frozen fixture. The
certificate proves this reduced task, not the original production or full-shape
kernel. The separate full-shape certificates use pinned human-developed lemmas.

| Reduced family | Requests | Outcome |
| --- | ---: | --- |
"""
        + "\n".join(rows)
        + f"""

The two disjoint batches share model revision `{summary["revision"]}`, TP=4,
seed 261102028, temperature 0, at most 16,384 output tokens, and a 4,096-token
reasoning limit. Every request/response and actual Lean check is archived.

- {summary["requests"]} requests and {summary["responses"]} responses.
- {summary["lean_checks"]} actual Lean checks; proposal-validation rejections are counted separately.
- {summary["reported_usage"]["prompt_tokens"]:,} reported prompt tokens + {summary["reported_usage"]["completion_tokens"]:,} completion tokens = **{summary["reported_usage"]["total_tokens"]:,}** total.
- **$0 hosted API spending**; local GPU time/electricity are not priced.

An uncertified proposal says the model did not prove the task in this harness
and budget. It does not say the kernel is buggy; deterministic certificates
already exist for all these reduced fixtures. The original models' registry,
agent tools, restart/review policies and stage traces are unavailable. Our
three-slot request combines obligations rather than reproducing the original
segmentation/equivalence agents or their forty-check budgets.

The earlier unbounded-reasoning pilot returned nine reasoning-only responses
and no Lean checks; its 32,768-token follow-up also returned no proof. Those
[different-budget runs](results/runtime-deepseek-20261109/) remain separate from
this cohort. `summarize_deepseek.py --lean /path/to/lean` audits both batches,
checks proposal provenance and reruns every successful certificate.
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
        json.dumps(
            {k: v for k, v in summary.items() if k not in ("cases", "verified_certificates")}
        )
    )


if __name__ == "__main__":
    main()
