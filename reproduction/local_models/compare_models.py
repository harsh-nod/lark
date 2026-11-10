"""Audit completed local cohorts and compare first attempts on the same 17 fixtures.

This reads recorded experiments only. It never makes an inference request.
Successful model proposals must survive another source-bound Lean recheck.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from lark_kernels.frontend import translate
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec
from reproduction.local_models import client
from reproduction.local_models.analyze_run import analyze
from reproduction.local_models.checkpoint import MODELS
from reproduction.local_models.run import SYSTEM

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
RESULTS = ROOT / "results"
IMAGE = (
    "vllm/vllm-openai-rocm@sha256:71a5d125b10a594752014b917a00cb1743387d1be9ee188aa1862af0b143c7dd"
)
COHORTS = {
    "deepseek": {
        "model": "deepseek-ai/DeepSeek-V4.1-Flash-1017",
        "tp": 4,
        "attempts": 3,
        "runs": [
            "pilot-deepseek-budget4096-20261109/deepseek-budget4096-remote",
            "pilot-deepseek-expanded-20261109/deepseek-budget4096-additional14-remote",
        ],
    },
    "glm_flash": {
        "model": "zai-org/GLM-5.3-Flash",
        "tp": 2,
        "attempts": 1,
        "runs": [
            "pilot-glm-flash-budget4096-20261109/glm-flash-budget4096-remote",
            "model-comparison-20261109/flash17-budget4096-half-a-remote",
            "model-comparison-20261109/flash17-budget4096-half-b-remote",
        ],
    },
    "glm": {
        "model": "zai-org/GLM-5.3",
        "tp": 4,
        "attempts": 3,
        "runs": [
            "model-comparison-20261109/glm53-budget4096-remote",
            "model-comparison-20261109/glm53-budget4096-half-a-remote",
            "model-comparison-20261109/glm53-budget4096-half-b-remote",
        ],
    },
}
CALL_STATUSES = {
    "proved",
    "unproved",
    "invalid-proposal",
    "no-proof-content",
    "transport-or-response-error",
}
NO_PROOF_FEEDBACK = "The previous response returned no final proof content. Submit concise JSON tactic candidates; Lean will check them."
INITIAL_FEEDBACK = "No proof has been proposed; write the three proofs from the fixed definitions."


class AuditError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(p):
    return json.loads(p.read_text())


def fixture_map():
    return {
        str(p.relative_to(REPO)): p
        for p in (REPO / "reproduction/nonlinear/cases/float16").iterdir()
        if (p / "task.json").is_file()
    }


def refusal_kind(content):
    """Describe the validator channel; markers are lexical, not bug diagnoses."""
    try:
        proposal = client.proposal(content)
    except (TypeError, ValueError, RecursionError):
        return {
            "channel": "json-or-top-level-schema",
            "native_decide_marker": False,
            "comment_marker": False,
        }
    proofs = proposal.get("proofs")
    if not isinstance(proofs, dict) or set(proofs) != set(certificate.DEFAULT_PROOFS):
        return {
            "channel": "proof-slot-schema",
            "native_decide_marker": False,
            "comment_marker": False,
        }
    texts = [p for p in proofs.values() if isinstance(p, str)]
    markers = {
        "native_decide_marker": any(re.search(r"\bnative_decide\b", p) for p in texts),
        "comment_marker": any("--" in p or "/-" in p for p in texts),
    }
    if any(
        not isinstance(p, str) or len(p) > 20000 or not p.strip().startswith("by")
        for p in proofs.values()
    ):
        return {"channel": "bounded-proof-slot-schema", **markers}
    try:
        certificate.validate_proofs(proofs)
    except ValueError:
        return {"channel": "proof-slot-policy", **markers}
    return {"channel": "segmentation-or-rendering", **markers}


def usage(records):
    keys = ("prompt_tokens", "completion_tokens", "total_tokens")
    known = {key: 0 for key in keys}
    incomplete, reasoning_incomplete, reasoning = False, False, 0
    for r in records:
        u = r.get("usage")
        complete = isinstance(u, dict) and all(type(u.get(k)) is int and u[k] >= 0 for k in keys)
        if complete:
            require(
                u["prompt_tokens"] + u["completion_tokens"] == u["total_tokens"],
                "Token totals disagree",
            )
        else:
            incomplete = True
        for key in keys:
            if isinstance(u, dict) and type(u.get(key)) is int:
                known[key] += u[key]
        d = u.get("completion_tokens_details") if isinstance(u, dict) else None
        n = d.get("reasoning_tokens") if isinstance(d, dict) else None
        if type(n) is not int:
            reasoning_incomplete = True
        else:
            require(
                n >= 0 and isinstance(u, dict) and n <= u["completion_tokens"],
                "Invalid reasoning-token count",
            )
            reasoning += n
    return {
        "reported_usage": known,
        "usage_incomplete": incomplete,
        "reported_reasoning_tokens": reasoning,
        "reasoning_usage_incomplete": reasoning_incomplete,
    }


def audit_run(root, *, lean=None):
    require(
        __debug__, "Run this auditor without Python -O; the frozen receipt audit uses assertions"
    )
    root = Path(root)
    report, server = load(root / "results.json"), load(root / "server.json")
    require(report["status"] == "finished", "Run is incomplete: " + str(root))
    # Preserve the existing receipt/hash audit, then establish stronger request,
    # provenance and first-attempt obligations below.
    original = analyze(root)
    client.endpoint(server["endpoint"])
    require(
        report["external_api_spend_usd"] == server["external_api_spend_usd"] == 0,
        "Unexpected external API spending",
    )
    fixtures = fixture_map()
    cases, rechecks, receipts, first_receipts, refusals = [], {}, [], [], []
    seen_receipts = set()
    require(server["revision"] == MODELS[report["model"]], "Checkpoint revision differs")
    require(server["image"] == IMAGE, "Serving image differs")
    require(
        report["reasoning_effort"] == ("low" if report["model"].startswith("zai-org/") else None),
        "Unexpected model-specific effort",
    )
    for i, case in enumerate(report["cases"]):
        require(case["case"] in fixtures, "Unknown fixture")
        fixture = fixtures[case["case"]]
        for key, name in (
            ("source_sha256", "kernel.hip"),
            ("reference_sha256", "reference.py"),
            ("task_sha256", "task.json"),
        ):
            require(
                sha((fixture / name).read_bytes()) == case[key], "Fixture bytes differ: " + name
            )
        task = Task.read(fixture / "task.json")
        tr = translate((fixture / "kernel.hip").read_text(), task)
        spec = read_spec((fixture / "reference.py").read_text(), task)
        current = {
            "segments": certificate.default_segments(tr.program),
            "proofs": {n: "by fail" for n in certificate.DEFAULT_PROOFS},
        }
        feedback = INITIAL_FEEDBACK
        calls = case["calls"]
        require(
            calls and [c["attempt"] for c in calls] == list(range(1, len(calls) + 1)),
            "Attempt sequence differs",
        )
        require(len(calls) <= report["attempts_per_case"], "Attempt budget exceeded")
        first_hash = None
        base = root / f"case-{i:02d}"
        for j, call in enumerate(calls):
            dest = base / f"attempt-{j + 1:02d}"
            receipt, request = load(dest / "receipt.json"), load(dest / "request.json")
            require(
                receipt["backend"] == "loopback-vllm"
                and receipt["endpoint"] == server["endpoint"]
                and receipt["model"] == report["model"],
                "Receipt backend/endpoint differs from the pinned local runtime",
            )
            seen_receipts.add(dest / "receipt.json")
            require(call["status"] in CALL_STATUSES, "Unknown call outcome")
            expected = {
                "program": [n.data() for n in tr.program],
                "proposal": current,
                "lean_source": certificate.render(task, tr, spec, current),
                "feedback": feedback,
                "instruction": "Return segments and the three proof slots only.",
            }
            messages = [
                {"role": "system", "content": SYSTEM},
                {"role": "user", "content": json.dumps(expected)},
            ]
            require(
                request["messages"] == messages,
                "Request does not match immutable statements/feedback",
            )
            require(request["stream"] is False, "Unexpected request mode")
            require(
                request.get("reasoning_effort") == report["reasoning_effort"],
                "Request effort differs",
            )
            receipts.append(receipt)
            if j == 0:
                first_receipts.append(receipt)
                first_hash = sha(json.dumps(messages, sort_keys=True, ensure_ascii=False).encode())
            response_path = dest / "response.json"
            content = (
                load(response_path)["choices"][0]["message"].get("content")
                if response_path.exists()
                else None
            )
            status = call["status"]
            if status in ("proved", "unproved"):
                require(response_path.exists(), "Lean check has no model response")
                proposal = client.proposal(content)
                require(
                    proposal == load(dest / "proposal.json"),
                    "Saved tactics differ from model response",
                )
                certificate.validate_proofs(proposal["proofs"])
                require(
                    (dest / "Main.lean").read_text()
                    == certificate.render(task, tr, spec, proposal),
                    "Attempt statement differs",
                )
                current = proposal
                feedback = (dest / "lean.log").read_text()
                require(
                    type(call["lean_timeout"]) is bool
                    and call["lean_timeout"] == ("Lean timed out" in feedback),
                    "Timeout flag differs",
                )
                require(
                    status != "proved" or j == len(calls) - 1,
                    "Run continued after a successful proof",
                )
            elif status == "invalid-proposal":
                require(
                    response_path.exists() and isinstance(content, str) and content.strip(),
                    "Invalid proposal has no returned content",
                )
                require(
                    not (dest / "lean.log").exists(),
                    "Invalid proposal incorrectly counted as Lean check",
                )
                refusals.append({"case": case["case"], "attempt": j + 1, **refusal_kind(content)})
                feedback = "Your proposal was refused: " + call["error"]
            elif status == "no-proof-content":
                require(
                    response_path.exists()
                    and (not isinstance(content, str) or not content.strip()),
                    "No-content outcome has final content",
                )
                require(
                    not (dest / "lean.log").exists(),
                    "No-content outcome incorrectly counted as Lean check",
                )
                feedback = NO_PROOF_FEEDBACK
            else:
                require(
                    not (dest / "lean.log").exists(),
                    "Transport outcome incorrectly counted as Lean check",
                )
        verified = case["status"] == "verified"
        require(
            verified == (calls[-1]["status"] == "proved"),
            "Case/call certification outcomes disagree",
        )
        require(
            verified or len(calls) == report["attempts_per_case"],
            "Uncertified case did not exhaust its recorded request budget",
        )
        if verified:
            require(lean is not None, "Lean is required to recheck a reported model success")
            cert = base / "certificate"
            require(
                load(cert / "proposal.json") == current,
                "Exported tactics differ from model response",
            )
            for target, source in (
                ("kernel.cu", "kernel.hip"),
                ("reference.py", "reference.py"),
                ("task.json", "task.json"),
            ):
                require(
                    (cert / target).read_bytes() == (fixture / source).read_bytes(),
                    "Exported fixture changed",
                )
            rechecks[fixture.name] = certificate.check(cert, lean=lean, timeout=150)
        first = calls[0]
        cases.append(
            {
                "case": case["case"],
                "first_outcome": first["status"],
                "first_verified": verified and len(calls) == 1,
                "first_messages_sha256": first_hash,
                "first_response_received": (base / "attempt-01/response.json").exists(),
                "requests": len(calls),
                "verified_within_recorded_budget": verified,
                "outcome": case["status"],
            }
        )
    require(
        seen_receipts == set(root.glob("case-*/attempt-*/receipt.json")),
        "Orphan or omitted request receipts",
    )
    require(
        sum(c["first_response_received"] for c in cases) <= report["inference_responses"],
        "Response count differs",
    )
    require(
        len(list(root.glob("case-*/attempt-*/response.json"))) == report["inference_responses"],
        "Response count differs",
    )
    u = usage(receipts)
    require(
        u["reported_usage"] == report["reported_usage"]
        and u["usage_incomplete"] == report["usage_incomplete"],
        "Reported token accounting differs",
    )
    return {
        "header": report,
        "server": server,
        "cases": cases,
        "call_outcomes": original["call_outcomes"],
        "lean_checks": original["lean_checks"],
        "requests": len(receipts),
        "responses": report["inference_responses"],
        "all_attempt_usage": u,
        "first_attempt_usage": usage(first_receipts),
        "proposal_refusals": refusals,
        "files": original["files"],
    }, rechecks


def audit_cohort(name, runs, *, lean):
    config = COHORTS[name]
    headers = [load(Path(p) / "results.json") for p in runs]
    expected = set(fixture_map())
    case_names = [c["case"] for h in headers for c in h["cases"]]
    require(len(case_names) == len(set(case_names)), "Duplicate cohort fixture")
    require(
        set(case_names) == expected and len(expected) == 17,
        "Cohort must cover exactly all 17 fixtures",
    )
    for h in headers:
        require(
            h["model"] == config["model"] and h["attempts_per_case"] == config["attempts"],
            "Cohort model/request budget differs",
        )
        for key in (
            "model",
            "runner_sha256",
            "client_sha256",
            "seed",
            "temperature",
            "max_tokens",
            "thinking_token_budget",
            "model_timeout_seconds",
            "lean_timeout_seconds",
            "reasoning_effort",
        ):
            require(h[key] == headers[0][key], "Inconsistent cohort setting: " + key)
    require(
        (
            headers[0]["seed"],
            headers[0]["temperature"],
            headers[0]["max_tokens"],
            headers[0]["thinking_token_budget"],
        )
        == (261102028, 0, 16384, 4096),
        "Unexpected nominal request settings",
    )
    audits, rechecks = [], {}
    for p in runs:
        a, logs = audit_run(Path(p), lean=lean)
        require(a["server"]["tensor_parallel"] == config["tp"], "Tensor parallelism differs")
        audits.append(a)
        rechecks.update(logs)
    cases = sorted((c for a in audits for c in a["cases"]), key=lambda c: c["case"])
    calls = Counter()
    for a in audits:
        calls.update(a["call_outcomes"])
    totals = {}
    for field in ("all_attempt_usage", "first_attempt_usage"):
        totals[field] = {
            "reported_usage": {
                k: sum(a[field]["reported_usage"][k] for a in audits)
                for k in ("prompt_tokens", "completion_tokens", "total_tokens")
            },
            "usage_incomplete": any(a[field]["usage_incomplete"] for a in audits),
            "reported_reasoning_tokens": sum(a[field]["reported_reasoning_tokens"] for a in audits),
            "reasoning_usage_incomplete": any(
                a[field]["reasoning_usage_incomplete"] for a in audits
            ),
        }
    return {
        "model": config["model"],
        "revision": MODELS[config["model"]],
        "tensor_parallel": config["tp"],
        "attempts_per_case": config["attempts"],
        "cases": cases,
        "first_attempt_certificates": sum(c["first_verified"] for c in cases),
        "first_attempt_responses": sum(c["first_response_received"] for c in cases),
        "first_attempt_outcomes": dict(Counter(c["first_outcome"] for c in cases)),
        "certificates_within_recorded_budget": sum(
            c["verified_within_recorded_budget"] for c in cases
        ),
        "requests": sum(a["requests"] for a in audits),
        "responses": sum(a["responses"] for a in audits),
        "lean_checks": sum(a["lean_checks"] for a in audits),
        "call_outcomes": dict(calls),
        "proposal_refusal_channels": dict(
            Counter(r["channel"] for a in audits for r in a["proposal_refusals"])
        ),
        "refused_proposals_with_native_decide_marker": sum(
            r["native_decide_marker"] for a in audits for r in a["proposal_refusals"]
        ),
        "refused_proposals_with_comment_marker": sum(
            r["comment_marker"] for a in audits for r in a["proposal_refusals"]
        ),
        "independent_certificate_rechecks": len(rechecks),
        "reasoning_effort_request": headers[0]["reasoning_effort"],
        "source_runs": [
            str(Path(p).relative_to(ROOT)) if Path(p).is_relative_to(ROOT) else str(p) for p in runs
        ],
        "source_run_files": {
            str(Path(p).relative_to(ROOT)) if Path(p).is_relative_to(ROOT) else str(p): a["files"]
            for p, a in zip(runs, audits)
        },
        **totals,
    }, rechecks


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model", choices=sorted(COHORTS), action="append")
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean", required=True)
    args = p.parse_args()
    require(not args.output.exists(), "Fresh output directory required")
    selected = args.model or list(COHORTS)
    require(len(selected) == len(set(selected)), "Duplicate selected model")
    paths = {n: [RESULTS / s for s in COHORTS[n]["runs"]] for n in selected}
    for roots in paths.values():
        for root in roots:
            require(
                (root / "results.json").is_file(), "Cohort evidence not yet available: " + str(root)
            )
            require(
                load(root / "results.json").get("status") == "finished",
                "Cohort still running: " + str(root),
            )
    models, logs = {}, {}
    for name in selected:
        models[name], logs[name] = audit_cohort(name, paths[name], lean=args.lean)
    pairs = {}
    for model in models.values():
        for case in model["cases"]:
            hashes = pairs.setdefault(case["case"], set())
            hashes.add(case["first_messages_sha256"])
            require(
                len(hashes) == 1,
                "Models did not receive the same first-attempt statements/messages",
            )
    args.output.mkdir(parents=True)
    for model, entries in logs.items():
        for name, log in entries.items():
            dest = args.output / "rechecks" / model / (name + ".log")
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(log)
    summary = {
        "schema": 1,
        "auditor_sha256": sha(Path(__file__).read_bytes()),
        "status": "audited-completed-local-cohorts",
        "three_model_comparison_complete": set(selected) == set(COHORTS),
        "original_paper_fully_reproduced": False,
        "models": models,
        "common_first_request_settings": {
            "seed": 261102028,
            "temperature": 0,
            "max_tokens": 16384,
            "thinking_token_budget": 4096,
            "cases": 17,
        },
        "same_first_attempt_messages_across_selected_models": True if len(selected) > 1 else None,
        "external_api_spend_usd": 0,
        "scope": "Independent reduced HIP fixtures and immutable proof-slot harness. Only first attempts are compared across models; later retry budgets differ. Tokenizers, templates, precision and TP differ; no isolated model-size or original-paper conclusion. Transport/empty/invalid outcomes remain separate from Lean rejections. All returned successes were independently rechecked.",
    }
    (args.output / "comparison.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "manifest.json").write_text(
        json.dumps(
            {
                str(p.relative_to(args.output)): sha(p.read_bytes())
                for p in sorted(args.output.rglob("*"))
                if p.is_file() and p.name != "manifest.json"
            },
            indent=2,
        )
        + "\n"
    )
    print(
        json.dumps(
            {
                "three_model_comparison_complete": summary["three_model_comparison_complete"],
                "models": {
                    n: {
                        k: m[k]
                        for k in (
                            "first_attempt_certificates",
                            "certificates_within_recorded_budget",
                            "requests",
                            "lean_checks",
                        )
                    }
                    for n, m in models.items()
                },
            }
        )
    )


if __name__ == "__main__":
    try:
        main()
    except (AuditError, AssertionError, OSError, ValueError, KeyError) as error:
        raise SystemExit("AUDIT FAILED: " + str(error))
