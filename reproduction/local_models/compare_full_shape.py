"""Aggregate complete independent cohorts using the paper's success-only costs.

This reads source-bound archived evidence. It does not rerun models, Lean or
GPUs, and it does not reproduce the original paper's registry or outcomes.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.local_models import audit_full_shape as audit  # noqa: E402
from reproduction.local_models import full_shape_run as run  # noqa: E402

MODELS = ("zai-org/GLM-5.3", "zai-org/GLM-5.3-Flash",
          "deepseek-ai/DeepSeek-V4.1-Flash-1017")
ROSTER = tuple(case[0] for case in run.full_shape.benchmark.CASES)
TOKEN_KEYS = ("prompt_tokens", "completion_tokens", "total_tokens")
require = run.require


def read(path):
    return json.loads(path.read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    path = PurePosixPath(name)
    return (name and not path.is_absolute() and str(path) == name
            and not {".", ".."} & set(path.parts))


def archive_files(root, archive_name, inventory_name):
    expected = read(root / inventory_name)
    require(isinstance(expected, dict) and all(safe_name(n) for n in expected),
            "Unsafe archive inventory")
    with tarfile.open(root / archive_name, "r:gz") as archive:
        members = archive.getmembers()
        require(len(members) == len(expected) and {m.name for m in members} == set(expected)
                and all(m.isfile() and safe_name(m.name) for m in members),
                "Archive inventory differs")
        files = {m.name: archive.extractfile(m).read() for m in members}
    require(all(digest(files[n]) == h for n, h in expected.items()),
            "Archive member bytes differ")
    return files


def token_usage(value):
    require(isinstance(value, dict)
            and all(type(value.get(k)) is int and value[k] >= 0 for k in TOKEN_KEYS)
            and value["total_tokens"] == value["prompt_tokens"] + value["completion_tokens"],
            "Missing, inconsistent or noninteger reported usage")
    return {key: value[key] for key in TOKEN_KEYS}


def sum_usage(rows):
    return {key: sum(row[key] for row in rows) for key in TOKEN_KEYS}


def case_summary(case, files, server):
    name = case["case"]
    calls = case["calls"]
    require(1 <= len(calls) <= run.PROTOCOL["request_budget"]
            and all(type(c["request"]) is int for c in calls)
            and [c["request"] for c in calls] == list(range(1, len(calls) + 1)),
            "Case request order/budget differs")
    allowed = {"library-read", "no-proof-content", "invalid-proposal", "unproved", "verified-proof"}
    require(all(c["status"] in allowed for c in calls), "Incomplete or unknown call outcome")
    checks = [c for c in calls if c["status"] in {"unproved", "verified-proof"}]
    reads = sum(c["status"] == "library-read" for c in calls)
    require(type(case["proof_checks"]) is type(case["library_reads"]) is int
            and case["proof_checks"] == len(checks) <= run.PROTOCOL["proof_check_budget"]
            and case["library_reads"] == reads <= run.PROTOCOL["library_read_budget"],
            "Actual proof-check/read counts differ")
    verified = case["status"] == "verified-proof"
    require(case["status"] in {"verified-proof", "budget-exhausted"}
            and verified == (calls[-1]["status"] == "verified-proof")
            and not any(c["status"] == "verified-proof" for c in calls[:-1]),
            "Case completion differs from its recorded calls")
    require(verified or len(calls) == run.PROTOCOL["request_budget"]
            or len(checks) == run.PROTOCOL["proof_check_budget"],
            "A failed case did not exhaust its fixed budget")
    usages = []
    for call in calls:
        folder = f"cases/{name}/call-{call['request']:02d}/model/"
        request, response = (files[folder + n] for n in ("request.json", "response.json"))
        receipt = json.loads(files[folder + "receipt.json"])
        require(receipt["request_sha256"] == digest(request)
                and receipt["response_sha256"] == digest(response), "Call receipt bytes differ")
        require(receipt["model"] == json.loads(request)["model"] == server["model"]
                and receipt["endpoint"] == server["endpoint"]
                and receipt["backend"] == "loopback-vllm"
                and receipt["external_api_spend_usd"] == 0, "Call model/endpoint/spending differs")
        usage = token_usage(receipt["usage"])
        require(usage == token_usage(json.loads(response)["usage"]),
                "Response and receipt usage differ")
        usages.append(usage)
    return {"case": name, "status": case["status"], "model_requests": len(calls),
            "library_reads": reads, "actual_lean_checks": len(checks),
            "first_response_verified": calls[0]["status"] == "verified-proof",
            "first_actual_lean_check_verified": bool(checks) and checks[0]["status"] == "verified-proof",
            "reported_usage": sum_usage(usages),
            "call_status_counts": dict(sorted(Counter(c["status"] for c in calls).items()))}


def load_packet(path):
    root = Path(path).resolve()
    require(not any(p.is_symlink() for p in root.rglob("*")), "Packet contains symlinks")
    manifest = read(root / "manifest.json")
    require(isinstance(manifest, dict) and all(safe_name(n) for n in manifest)
            and {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
            == set(manifest) | {"manifest.json"}, "Packet inventory differs")
    require(all(run.sha(root / n) == h for n, h in manifest.items()), "Packet bytes differ")
    summary, raw, replay, binding = (read(root / n) for n in (
        "results.json", "raw-results.json", "audit-results.json", "binding.json"))
    require(summary["schema"] == raw["schema"] == 1 and run.cohort_complete(raw)
            and summary["complete_17_case_cohort"] is True and raw["test_stub"] is False
            and summary["test_stub"] is False, "A complete non-stub seventeen-case cohort is required")
    language = run.PREPARATIONS.get(raw["preparation_manifest_sha256"])
    require(language in {"hip", "cuda"} and summary["source_language"]
            == raw.get("source_language", "hip") == language, "Preparation/source language differs")
    allowed_producers = {"0e49b6ce519a2af91c81ee60419adcf37357a71fdf904a772dab0cd279368aef",
                         "05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1"}
    require(raw["runner_sha256"] in allowed_producers
            and language in audit.RUNNERS[raw["runner_sha256"]], "Unknown full-cohort controller")
    model = raw["model"]
    require(model in MODELS and summary["model"] == model
            and summary["revision"] == raw["revision"] == run.MODELS[model], "Model/revision differs")
    require(summary["protocol"] == raw["protocol"] == run.PROTOCOL,
            "Cohort proof/model budgets differ")
    require(all(row["original_paper_fully_reproduced"] is False
                for row in (summary, raw, replay, binding)), "Original-paper completion overclaim")
    require(summary["external_api_spend_usd"] == raw["external_api_spend_usd"]
            == raw["new_source_certificates"] == summary["new_registered_source_certificates"]
            == raw["gpu_trials"] == summary["gpu_trials"] == 0,
            "Unexpected spending, GPU trials or new source certificates")
    preparation = "full-shape-preparation-v2" if language == "hip" else "full-shape-cuda-preparation-v1"
    require(binding["preparation_archive_sha256"] == run.sha(
        ROOT / "reproduction/local_models/results" / preparation / "preparation.tar.gz"),
        "Pinned preparation archive differs")
    files = archive_files(root, "cohort.tar.gz", "cohort-files.json")
    checks = archive_files(root, "audit.tar.gz", "audit-files.json")
    require(json.loads(files["results.json"]) == raw
            and json.loads(checks["results.json"]) == replay, "Archive/external report disagreement")
    require(digest(files["runner.py"]) == raw["runner_sha256"]
            and digest(files["client.py"]) == raw["client_sha256"] == run.sha(Path(run.client.__file__)),
            "Captured producer/client differs")
    server = json.loads(files["server.json"])
    require(digest(files["server.json"]) == raw["server_record_sha256"]
            and server["status"] == "ready" and server["model"] == model
            and server["revision"] == raw["revision"] and server["image"] == run.IMAGE
            and re.fullmatch(r"[0-9a-f]{64}", server["container_id"])
            and server["max_model_len"] >= run.PROTOCOL["context_limit"], "Pinned runtime differs")
    run.client.endpoint(server["endpoint"])
    rows = [case_summary(case, files, server) for case in raw["cases"]]
    require(tuple(row["case"] for row in rows) == ROSTER and rows == summary["cases"]
            and all(type(row[k]) is bool for row in summary["cases"]
                    for k in ("first_response_verified", "first_actual_lean_check_verified")),
            "Per-case summary differs from actual calls/receipts")
    declared_calls = {f"cases/{c['case']}/call-{i:02d}/model/request.json"
                      for c in rows for i in range(1, c["model_requests"] + 1)}
    require({n for n in files if re.fullmatch(r"cases/[^/]+/call-[0-9]+/model/request\.json", n)}
            == declared_calls, "Unaccounted model request")
    winners = [c for c in rows if c["status"] == "verified-proof"]
    usage = sum_usage([c["reported_usage"] for c in rows])
    requests = sum(c["model_requests"] for c in rows)
    counts = {"cases": 17, "verified_within_budget": len(winners),
              "budget_exhausted": 17 - len(winners),
              "first_response_verified": sum(c["first_response_verified"] for c in rows),
              "first_actual_lean_check_verified": sum(c["first_actual_lean_check_verified"] for c in rows),
              "actual_lean_checks": sum(c["actual_lean_checks"] for c in rows),
              "model_requests": requests, "response_files": requests,
              "raw_files": len(files), "audit_files": len(checks),
              "additional_fresh_kernel_checks": 2 * len(winners)}
    require(summary["counts"] == counts and all(type(v) is int for v in summary["counts"].values())
            and summary["reported_usage"] == raw["reported_usage"]
            == replay["reported_usage"] == usage and summary["usage_incomplete"] is False
            and raw["usage_incomplete"] is False and raw["request_attempts"]
            == raw["response_files"] == raw["model_inference_calls"] == requests
            and raw["verified_model_proofs"] == len(winners), "Cohort totals/usage differ")
    require(replay["status"] == "recorded-full-size-protocol-replayed"
            and replay["complete_17_case_cohort"] is True
            and replay["recording_results_sha256"] == run.sha(root / "raw-results.json")
            and replay["preparation_manifest_sha256"] == raw["preparation_manifest_sha256"]
            == summary["preparation_manifest_sha256"]
            and replay["source_language"] == language and replay["model"] == model
            and tuple(replay["selected_cases"]) == tuple(replay["replayed_cases"]) == ROSTER
            and replay["recorded_verified_model_proofs"] == replay["freshly_verified_model_proofs"]
            == len(winners) and len(replay["bound_model_requests"]) == requests
            and replay["auditor_sha256"] == run.sha(Path(audit.__file__))
            and replay["controller_sha256"] == run.sha(Path(run.__file__))
            and replay["model_calls_by_audit"] == replay["external_api_spend_usd"]
            == replay["new_registered_source_certificates"] == 0,
            "Complete fresh accepted-proof audit binding differs")
    expected_fresh = set()
    for row in winners:
        original = f"cases/{row['case']}/call-{row['model_requests']:02d}/proof-check/Main.lean"
        prefix = f"protocol-replay/{row['case']}/call-{row['model_requests']:02d}/"
        require(prefix + "fresh-proof-syntax.log" in checks, "Fresh proof parser log missing")
        for number in (1, 2):
            folder = prefix + f"fresh-kernel-{number}"
            require(checks[folder + "/Main.lean"] == files[original]
                    and checks[folder + "/lean.log"], "Fresh accepted Main/log differs")
            expected_fresh.add(folder)
    require(len(replay["fresh_accepted_proof_kernel_checks"]) == len(expected_fresh)
            and set(replay["fresh_accepted_proof_kernel_checks"]) == expected_fresh,
            "Fresh proof-check roster differs")
    require(binding["raw_results_sha256"] == run.sha(root / "raw-results.json")
            and binding["audit_results_sha256"] == run.sha(root / "audit-results.json")
            and binding["raw_runner_sha256"] == raw["runner_sha256"]
            and binding["client_sha256"] == raw["client_sha256"]
            and binding["auditor_sha256"] == replay["auditor_sha256"]
            and binding["auditor_replay_controller_sha256"] == replay["controller_sha256"]
            and binding["all_model_requests_bound_to_fixed_protocol"] is True
            and binding["accepted_raw_tactics_bound_to_both_original_and_fresh_Mains"] is True
            and binding["failed_lean_candidates_freshly_rechecked"] is False
            and replay["failed_candidates_freshly_rechecked"] is False,
            "Producer/auditor binding differs")
    return {"model": model, "revision": raw["revision"], "source_language": language,
            "packet_id": root.name, "packet_manifest_sha256": run.sha(root / "manifest.json"),
            "preparation_manifest_sha256": raw["preparation_manifest_sha256"],
            "cohort_reported_usage": usage, "recorded_counts": counts, "cases": rows}


def level_stats(rows):
    winners = [r for r in rows if r["status"] == "verified-proof"]
    successful_usage = sum_usage([r["reported_usage"] for r in winners])
    return {"tasks": len(rows), "verified_within_budget": len(winners),
            "budget_exhausted": len(rows) - len(winners),
            "pass_rate": len(winners) / len(rows) if rows else None,
            "all_task_reported_usage": sum_usage([r["reported_usage"] for r in rows]),
            "successful_task_reported_usage": successful_usage,
            "mean_over_verified_tasks_tokens": {
                k: successful_usage[k] / len(winners) if winners else None for k in TOKEN_KEYS},
            "mean_denominator_verified_tasks": len(winners),
            "first_response_verified": sum(r["first_response_verified"] for r in rows),
            "first_actual_lean_check_verified": sum(r["first_actual_lean_check_verified"] for r in rows)}


def compare(packets, allow_partial=False):
    inputs = [load_packet(path) for path in packets]
    require(inputs, "At least one complete cohort packet is required")
    keys = [(r["model"], r["source_language"]) for r in inputs]
    require(len(set(keys)) == len(keys), "Duplicate model/language cohort")
    missing = [{"model": model, "source_language": language}
               for model in MODELS for language in ("hip", "cuda") if (model, language) not in keys]
    require(allow_partial or not missing, "Missing independent cohorts; explicitly allow a partial roster")
    for row in inputs:
        row["levels"] = {"level1": level_stats(row["cases"][:12]),
                         "level2": level_stats(row["cases"][12:])}
    return {"schema": 1, "status": "partial-independent-full-size-comparison" if missing
            else "six-independent-full-size-cohorts-compared",
            "created_at_utc": datetime.now(timezone.utc).isoformat(),
            "comparison_driver_sha256": run.sha(Path(__file__)), "protocol": run.PROTOCOL,
            "expected_independent_cohorts": 6, "complete_independent_cohorts": len(inputs),
            "all_six_independent_cohorts_present": not missing, "missing_cohorts": missing,
            "inputs": inputs, "level1_cases": list(ROSTER[:12]), "level2_cases": list(ROSTER[12:]),
            "model_calls_by_comparison": 0, "fresh_lean_checks_by_comparison": 0,
            "gpu_trials_by_comparison": 0, "new_registered_source_certificates": 0,
            "external_api_spend_usd": 0, "original_paper_fully_reproduced": False,
            "metric_definition": "Mean input/output token costs include all responses, reads and failed proposals of each eventually verified task; budget-exhausted tasks are excluded from those means. All-task cohort totals retain failed-task costs. First response and first actual Lean check are separate metrics.",
            "scope": "Independent fixed-scaffold tasks and existing generic proof libraries, three pinned open models and HIP/CUDA sources. Level2 includes dense SDPA, not the original FlashAttention algorithm. Packet hashes and recorded fresh-check bindings are checked here; no model/protocol/Lean/GPU experiment is rerun. This is not the original registry, PTX, closed-model histories, 144-cell result or NVIDIA measurement."}


def markdown(report):
    lines = ["# Independent full-size model comparison", "",
             "**The original paper is not fully reproduced.** These are separate fixed-scaffold experiments.", "",
             f"Complete independent cohorts supplied: {report['complete_independent_cohorts']} of 6; this is not a paper-completion denominator.", "",
             "| Model | Source | Level | Verified / tasks | Mean input M tokens, verified tasks | Mean output M tokens, verified tasks |",
             "| --- | --- | --- | ---: | ---: | ---: |"]
    for row in report["inputs"]:
        for level, stats in row["levels"].items():
            mean = stats["mean_over_verified_tasks_tokens"]
            values = ["n/a" if mean[k] is None else f"{mean[k] / 1e6:.6f}"
                      for k in ("prompt_tokens", "completion_tokens")]
            lines.append(f"| {row['model']} | {row['source_language']} | {level} | "
                         f"{stats['verified_within_budget']} / {stats['tasks']} | {values[0]} | {values[1]} |")
    lines += ["", "Cohort totals below include every task, including budget exhaustions.", "",
              "| Model | Source | Requests | All-task input M tokens | All-task output M tokens | First response / first actual Lean check verified |",
              "| --- | --- | ---: | ---: | ---: | ---: |"]
    for row in report["inputs"]:
        counts, usage = row["recorded_counts"], row["cohort_reported_usage"]
        lines.append(f"| {row['model']} | {row['source_language']} | {counts['model_requests']} | "
                     f"{usage['prompt_tokens'] / 1e6:.6f} | {usage['completion_tokens'] / 1e6:.6f} | "
                     f"{counts['first_response_verified']} / {counts['first_actual_lean_check_verified']} |")
    lines += ["", report["metric_definition"], "", report["scope"], ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", action="append", required=True, type=Path)
    parser.add_argument("--allow-partial-roster", action="store_true")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.exists() and not any((p / ".git").exists() for p in (output, *output.parents)),
            "Comparison output must be fresh and outside Git")
    report = compare(args.packet, args.allow_partial_roster)
    output.mkdir(parents=True)
    run.write(output / "results.json", report)
    (output / "RESULTS.md").write_text(markdown(report))
    run.write(output / "manifest.json", {p.name: run.sha(p) for p in sorted(output.iterdir()) if p.is_file()})
    print(json.dumps({k: report[k] for k in ("status", "complete_independent_cohorts",
                                           "all_six_independent_cohorts_present")}))


if __name__ == "__main__":
    main()
