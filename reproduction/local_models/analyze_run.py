"""Audit complete local proof-pilot receipts without conflating outcome classes."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def analyze(root):
    report = json.loads((root / "results.json").read_text())
    assert report["status"] == "finished"
    server = json.loads((root / "server.json").read_text())
    assert (
        server["status"] == "ready" and sha(root / "server.json") == report["server_record_sha256"]
    )
    assert server["model"] == report["model"]
    calls, receipts, lean_checks, no_content = Counter(), [], 0, 0
    files = {}
    for i, case in enumerate(report["cases"]):
        base = root / f"case-{i:02d}"
        assert json.loads((base / "result.json").read_text()) == case
        assert case["revision"] == server["revision"] and case["model"] == report["model"]
        for call in case["calls"]:
            dest = base / f"attempt-{call['attempt']:02d}"
            receipt = json.loads((dest / "receipt.json").read_text())
            request = json.loads((dest / "request.json").read_text())
            assert sha(dest / "request.json") == receipt["request_sha256"]
            assert request["model"] == server["model"] and request["seed"] == report["seed"]
            assert (
                request["max_tokens"] == report["max_tokens"]
                and request["temperature"] == report["temperature"]
            )
            assert request.get("thinking_token_budget") == report.get("thinking_token_budget")
            assert receipt["external_api_spend_usd"] == 0
            if (dest / "response.json").exists():
                assert sha(dest / "response.json") == receipt["response_sha256"]
                response = json.loads((dest / "response.json").read_text())
                assert response["model"] == server["model"] and response.get(
                    "usage"
                ) == receipt.get("usage")
                content = response["choices"][0]["message"].get("content")
                if call["status"] == "no-proof-content":
                    assert not isinstance(content, str) or not content.strip()
                    assert not (dest / "lean.log").exists()
                    no_content += 1
            if (dest / "lean.log").exists():
                assert (dest / "Main.lean").is_file() and (dest / "proposal.json").is_file()
                lean_checks += 1
            calls[call["status"]] += 1
            receipts.append(receipt)
    keys = ("prompt_tokens", "completion_tokens", "total_tokens")
    usage = {
        k: sum(r.get("usage", {}).get(k, 0) for r in receipts if isinstance(r.get("usage"), dict))
        for k in keys
    }
    assert usage == report["reported_usage"] and len(receipts) == report["request_attempts"]
    for p in sorted(root.rglob("*")):
        if p.is_file():
            files[str(p.relative_to(root))] = sha(p)
    return {
        "schema": 1,
        "status": "audited-complete-independent-run",
        "model": report["model"],
        "revision": server["revision"],
        "cases": len(report["cases"]),
        "case_outcomes": dict(Counter(c["status"] for c in report["cases"])),
        "call_outcomes": dict(calls),
        "requests": len(receipts),
        "responses": report["inference_responses"],
        "no_proof_content": no_content,
        "lean_checks": lean_checks,
        "verified_certificates": sum(c["status"] == "verified" for c in report["cases"]),
        "usage_incomplete": report["usage_incomplete"],
        "reported_usage": usage,
        "reported_reasoning_tokens": sum(
            (r.get("usage", {}).get("completion_tokens_details") or {}).get("reasoning_tokens", 0)
            for r in receipts
            if isinstance(r.get("usage"), dict)
        ),
        "request_elapsed_seconds": sum(r["elapsed_seconds"] for r in receipts),
        "max_tokens": report["max_tokens"],
        "thinking_token_budget": report.get("thinking_token_budget"),
        "external_api_spend_usd": 0,
        "scope": "Independent reduced HIP immutable-proof-slot experiment, not original registry, harness, endpoints, pass rates, token costs or failure diagnosis. Only actual Lean checks count as proof checks.",
        "files": files,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--run", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.output.exists() or args.output.resolve().is_relative_to(args.run.resolve()):
        p.error("fresh output outside the immutable run directory required")
    args.output.write_text(json.dumps(analyze(args.run), indent=2) + "\n")


if __name__ == "__main__":
    main()
