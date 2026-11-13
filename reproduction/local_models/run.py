"""Independent local-model proof experiment; the original paper harness is absent.

Models return bounded JSON tactic proposals. This process owns files and Lean
checks. Models receive no tools, shell access, or permission to edit statements
or GPU sources.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels import certificate
from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import preflight
from lark_kernels.spec import read_spec
from reproduction.local_models import client

ROOT = Path(__file__).resolve().parents[2]
SYSTEM = """Write Lean 4.19.0 proofs for the supplied fixed GPU-machine statements.
Return exactly one JSON object with keys segments and proofs. The proofs object
has exactly segmentation_data, race_free, and segment_equivalence. Every proof
starts with by. Segments refer to the supplied flat instruction indices.
The machine, program, specification and assumptions are immutable. Use Std only.
No sorry, admit, axioms, declarations, native_decide, metaprogramming, IO or tools.
All scalar operations are arbitrary: do not assume algebraic laws.
You may use definitional reduction to relate execution to finalState and traceData,
then prove the concrete trace's raceFree predicate. A successful equivalence must
cover every input and arbitrary outside memory, and successful completion.
Your response is untrusted and Lean independently checks it. Return JSON only.
"""


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def run_case(case, output, args, server):
    output.mkdir(parents=True, exist_ok=False)
    kernel, reference, task_path = case / "kernel.hip", case / "reference.py", case / "task.json"
    task = Task.read(task_path)
    tr = translate(kernel.read_text(), task)
    spec = read_spec(reference.read_text(), task)
    preflight(task, tr, spec)
    binary = certificate.lean_binary(args.lean)
    current = {
        "segments": certificate.default_segments(tr.program),
        "proofs": {name: "by fail" for name in certificate.DEFAULT_PROOFS},
    }
    feedback = "No proof has been proposed; write the three proofs from the fixed definitions."
    result = {
        "case": str(case.relative_to(ROOT)),
        "status": "unproved",
        "calls": [],
        "source_sha256": sha(kernel),
        "reference_sha256": sha(reference),
        "task_sha256": sha(task_path),
        "model": args.model,
        "revision": server["revision"],
    }
    for attempt in range(1, args.attempts + 1):
        destination = output / f"attempt-{attempt:02d}"
        start = time.monotonic()
        request = {
            "program": [i.data() for i in tr.program],
            "proposal": current,
            "lean_source": certificate.render(task, tr, spec, current),
            "feedback": feedback,
            "instruction": "Return segments and the three proof slots only.",
        }
        row = {"attempt": attempt}
        try:
            content = client.call(
                args.url,
                args.model,
                [
                    {"role": "system", "content": SYSTEM},
                    {"role": "user", "content": json.dumps(request)},
                ],
                destination,
                seed=args.seed,
                temperature=args.temperature,
                max_tokens=args.max_tokens,
                timeout=args.model_timeout,
                reasoning_effort=getattr(args, "reasoning_effort", "max"),
                thinking_token_budget=getattr(args, "thinking_token_budget", None),
            )
        except Exception as error:
            no_content = (
                str(error) == "Model produced no proof content"
                and (destination / "response.json").is_file()
            )
            row.update(
                status="no-proof-content" if no_content else "transport-or-response-error",
                error=str(error),
                elapsed_seconds=time.monotonic() - start,
            )
            if no_content:
                feedback = "The previous response returned no final proof content. Submit concise JSON tactic candidates; Lean will check them."
            else:
                try:
                    client.check_health(args.url, args.model)
                except Exception as health_error:
                    result["status"] = "runtime-unavailable"
                    row["runtime_health_error"] = str(health_error)
            result["calls"].append(row)
            write(output / "result.json", result)
            print(json.dumps({"case": case.name, **row}), flush=True)
            if result["status"] == "runtime-unavailable":
                return result
            continue
        try:
            candidate = client.proposal(content)
            certificate.validate_proofs(candidate["proofs"])
            lean_source = certificate.render(task, tr, spec, candidate)
        except (ValueError, Refusal, KeyError, TypeError, RecursionError) as error:
            row.update(status="invalid-proposal", error=str(error))
            feedback = "Your proposal was refused: " + str(error)
        else:
            current = candidate
            (destination / "Main.lean").write_text(lean_source)
            write(destination / "proposal.json", current)
            from lark_kernels.proof_syntax import check_terms

            syntax_ok, feedback = check_terms(current["proofs"], binary, args.lean_timeout)
            (destination / "proof-syntax.log").write_text(feedback)
            if syntax_ok:
                ok, feedback = certificate.run_lean(destination, binary, args.lean_timeout)
            else:
                ok = False
            (destination / "lean.log").write_text(feedback)
            row.update(
                status=("proved" if ok else "unproved") if syntax_ok else "invalid-proposal",
                proof_term_syntax_accepted=syntax_ok,
                lean_timeout="Lean timed out" in feedback,
            )
            if ok:
                # Independent second invocation constructs/rechecks the public
                # certificate from the original bytes and this exact proposal.
                proof = certificate.verify(
                    kernel,
                    reference,
                    task_path,
                    output / "certificate",
                    lean=args.lean,
                    timeout=args.lean_timeout,
                    proposal_path=destination / "proposal.json",
                )
                if proof["status"] != "verified":
                    raise RuntimeError("A successful proposal failed independent export")
                certificate.check(output / "certificate", lean=args.lean, timeout=args.lean_timeout)
                result["status"] = "verified"
        row["elapsed_seconds"] = time.monotonic() - start
        result["calls"].append(row)
        write(output / "result.json", result)
        print(json.dumps({"case": case.name, **row}), flush=True)
        if result["status"] == "verified":
            break
    if result["status"] != "verified":
        if all(row["status"] == "no-proof-content" for row in result["calls"]):
            result["status"] = "no-proof-content"
        elif all(row["status"] == "transport-or-response-error" for row in result["calls"]):
            result["status"] = "no-model-response"
        elif not any(row["status"] == "unproved" for row in result["calls"]):
            result["status"] = "invalid-proposals"
        write(output / "result.json", result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--url", required=True)
    p.add_argument("--model", required=True, choices=sorted(client.MODELS))
    p.add_argument("--server-record", required=True, type=Path)
    p.add_argument("--case", action="append", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--lean", required=True)
    p.add_argument("--attempts", type=int, default=3)
    p.add_argument("--seed", type=int, default=261102028)
    p.add_argument("--temperature", type=float, default=0)
    p.add_argument("--max-tokens", type=int, default=16384)
    p.add_argument("--model-timeout", type=float, default=600)
    p.add_argument("--lean-timeout", type=float, default=150)
    p.add_argument("--reasoning-effort", choices=("low", "high", "max"), default="max")
    p.add_argument(
        "--thinking-token-budget",
        type=int,
        help="Optional vLLM reasoning-token limit; recorded as a separate experiment setting",
    )
    args = p.parse_args()
    client.endpoint(args.url)
    if not 1 <= args.attempts <= 16:
        p.error("attempts must be 1..16")
    if args.thinking_token_budget is not None and (
        args.thinking_token_budget < 0 or args.thinking_token_budget >= args.max_tokens
    ):
        p.error("thinking-token-budget must be nonnegative and smaller than max-tokens")
    server = json.loads(args.server_record.read_text())
    if (
        server["model"] != args.model
        or not server.get("revision")
        or server.get("status") != "ready"
    ):
        p.error(
            "server record must identify the requested checkpoint revision and passed health checks"
        )
    args.output.mkdir(parents=True, exist_ok=False)
    write(args.output / "server.json", server)
    report = {
        "schema": 1,
        "experiment": "independent-local-model-proof-proposals",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "model": args.model,
        "server_record_sha256": sha(args.server_record),
        "runner_sha256": sha(Path(__file__)),
        "client_sha256": sha(Path(client.__file__)),
        "seed": args.seed,
        "temperature": args.temperature,
        "max_tokens": args.max_tokens,
        "attempts_per_case": args.attempts,
        "model_timeout_seconds": args.model_timeout,
        "lean_timeout_seconds": args.lean_timeout,
        "reasoning_effort": args.reasoning_effort if args.model.startswith("zai-org/") else None,
        "thinking_token_budget": args.thinking_token_budget,
        "external_api_spend_usd": 0,
        "cases": [],
        "scope": "Our reduced HIP programs and bounded proof-slot harness. Not the authors' registry, harness, endpoint, pass rates, token costs, failure-analysis or segmentation ablations.",
    }
    for i, case in enumerate(args.case):
        try:
            report["live_models"] = client.check_health(args.url, args.model)
        except Exception as error:
            report.update(status="runtime-unavailable", health_error=str(error))
            write(args.output / "results.json", report)
            print(json.dumps({"status": "runtime-unavailable", "error": str(error)}), flush=True)
            return
        report["cases"].append(
            run_case(case.resolve(), args.output / f"case-{i:02d}", args, server)
        )
        write(args.output / "results.json", report)
        if report["cases"][-1]["status"] == "runtime-unavailable":
            break
    report["status"] = (
        "runtime-unavailable"
        if any(r["status"] == "runtime-unavailable" for r in report["cases"])
        else "finished"
    )
    receipts = [
        json.loads(path.read_text()) for path in args.output.glob("case-*/attempt-*/receipt.json")
    ]
    report["request_attempts"] = len(receipts)
    report["inference_responses"] = len(list(args.output.glob("case-*/attempt-*/response.json")))
    keys = ("prompt_tokens", "completion_tokens", "total_tokens")
    report["usage_incomplete"] = any(
        not isinstance(r.get("usage"), dict)
        or any(type(r["usage"].get(key)) is not int for key in keys)
        for r in receipts
    )
    report["reported_usage"] = {
        key: sum(
            r["usage"][key]
            for r in receipts
            if isinstance(r.get("usage"), dict) and type(r["usage"].get(key)) is int
        )
        for key in keys
    }
    write(args.output / "results.json", report)


if __name__ == "__main__":
    main()
