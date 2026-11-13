"""Check recorded full-size model summaries for the frozen paper ledger.

This checks report, inventory, metric and recorded replay consistency. The linked
cohort packets and compare_full_shape.py retain the stricter raw-response and
protocol validators. This module runs no inference, Lean or GPU experiment.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[2]
MODELS = {
    "zai-org/GLM-5.3": "ba32f8c19c8738e2c57c71798c601d477a7bf844",
    "zai-org/GLM-5.3-Flash": "46a050bec13002ad29ee795c16e61cf4fa3c4a9c",
    "deepseek-ai/DeepSeek-V4.1-Flash-1017": "1bae0e1088993b9b82de08f59de5be5a34e42170",
}
CASES = ["relu", "silu", "gelu", "rmsnorm", "layernorm", "softmax", "gemv",
         "gemm", "bmm", "linear", "conv2d", "depthwise_conv", "rope", "ffn",
         "swiglu", "attention", "gqa"]
TOKENS = ("prompt_tokens", "completion_tokens", "total_tokens")
PROTOCOL = {
    "version": "full-shape-bounded-library-reads-v1", "request_budget": 16,
    "proof_check_budget": 3, "library_read_budget": 8, "max_read_lines": 120,
    "max_tokens": 16384, "thinking_token_budget": 4096, "seed": 261102028,
    "temperature": 0, "reasoning_effort": "low", "context_limit": 65536,
    "context_margin": 256, "model_timeout_seconds": 1800,
    "lean_timeout_seconds": 180, "feedback_chars": 12000, "last_response_chars": 8000,
}


def check_full_shape_evidence(config, root=ROOT):
    """Validate the declared complete cohorts, keeping missing cohorts explicit."""
    def require(ok, message):
        if not ok:
            raise ValueError("Full-shape model " + message)

    def digest(data):
        return hashlib.sha256(data).hexdigest()

    declared = {path for group in config["evidence_groups"].values() for path in group}
    root = Path(root).resolve()

    def content(name):
        path = PurePosixPath(name)
        require(name in declared and not path.is_absolute() and ".." not in path.parts
                and str(path) == name, "evidence path differs")
        local = root / name
        require(local.is_file() and not local.is_symlink()
                and local.resolve().is_relative_to(root), "evidence path differs")
        return local.read_bytes()

    def read(name):
        return json.loads(content(name))

    def usage(row):
        require(isinstance(row, dict) and all(type(row.get(k)) is int and row[k] >= 0
                for k in TOKENS) and row["total_tokens"] == row["prompt_tokens"]
                + row["completion_tokens"], "reported token usage differs")
        return {k: row[k] for k in TOKENS}

    def summed(rows):
        values = [usage(row) for row in rows]
        return {k: sum(row[k] for row in values) for k in TOKENS}

    def levels(rows):
        winners = [row for row in rows if row["status"] == "verified-proof"]
        total = summed([row["reported_usage"] for row in winners])
        return {
            "tasks": len(rows), "verified_within_budget": len(winners),
            "budget_exhausted": len(rows) - len(winners),
            "pass_rate": len(winners) / len(rows),
            "all_task_reported_usage": summed([row["reported_usage"] for row in rows]),
            "successful_task_reported_usage": total,
            "mean_over_verified_tasks_tokens": {
                k: total[k] / len(winners) if winners else None for k in TOKENS},
            "mean_denominator_verified_tasks": len(winners),
            "first_response_verified": sum(row["first_response_verified"] for row in rows),
            "first_actual_lean_check_verified": sum(
                row["first_actual_lean_check_verified"] for row in rows),
        }

    spec = config["full_shape_models"]
    count = spec["required_cohorts"]
    require(type(count) is int and 1 <= count <= 6 and len(spec["packets"]) == count,
            "declared cohort count differs")
    prefix = spec["comparison_prefix"]
    report, binding, manifest = (read(prefix + "/" + name) for name in
                                ("results.json", "binding.json", "manifest.json"))
    require(set(manifest) == {"results.json", "binding.json", "RESULTS.md"}
            and all(digest(content(prefix + "/" + name)) == value
                    for name, value in manifest.items()), "comparison file binding differs")
    require(report["expected_independent_cohorts"] == 6
            and report["complete_independent_cohorts"] == count
            and len(report["inputs"]) == count
            and report["level1_cases"] == CASES[:12] and report["level2_cases"] == CASES[12:]
            and report["protocol"] == PROTOCOL, "comparison roster/protocol differs")
    require(report["original_paper_fully_reproduced"] is False
            and binding["original_paper_fully_reproduced"] is False
            and all(type(report[k]) is int and report[k] == 0 for k in (
                "model_calls_by_comparison", "fresh_lean_checks_by_comparison",
                "gpu_trials_by_comparison", "new_registered_source_certificates",
                "external_api_spend_usd")), "comparison execution/original scope differs")
    require(report["comparison_driver_sha256"] == binding["driver_sha256"]
            == digest(content(binding["driver_source_path"])), "comparison driver binding differs")
    keys, records, outcomes, totals = set(), [], [], []
    for expected, row in zip(spec["packets"], report["inputs"], strict=True):
        packet = expected["prefix"]
        packet_manifest = read(packet + "/manifest.json")
        require(digest(content(packet + "/manifest.json"))
                == expected["manifest_sha256"] == row["packet_manifest_sha256"]
                and row["packet_id"] == PurePosixPath(packet).name,
                "packet manifest binding differs")
        names = ("results.json", "raw-results.json", "audit-results.json", "binding.json",
                 "cohort-files.json", "audit-files.json")
        require(all(digest(content(packet + "/" + name)) == packet_manifest[name]
                    for name in names), "packet report binding differs")
        summary, raw, audit, proof, files, checks = (read(packet + "/" + name) for name in names)
        language = raw.get("source_language", "hip")
        key = (raw["model"], language)
        require(key not in keys and key[0] in MODELS and language in ("hip", "cuda")
                and summary["model"] == row["model"] == audit["model"] == key[0]
                and summary["source_language"] == row["source_language"] == language
                and summary["revision"] == row["revision"] == raw["revision"] == MODELS[key[0]],
                "model/language/revision identity differs")
        keys.add(key)
        require(summary["complete_17_case_cohort"] is raw["complete_17_case_cohort"]
                is audit["complete_17_case_cohort"] is True
                and summary["test_stub"] is raw["test_stub"] is False
                and summary["usage_incomplete"] is raw["usage_incomplete"] is False
                and raw["status"] == "finished"
                and summary["protocol"] == raw["protocol"] == PROTOCOL,
                "complete non-stub fixed protocol differs")
        require(all(item["original_paper_fully_reproduced"] is False
                    for item in (summary, raw, audit, proof))
                and summary["new_registered_source_certificates"] == summary["gpu_trials"]
                == summary["external_api_spend_usd"] == raw["new_source_certificates"]
                == raw["gpu_trials"] == audit["model_calls_by_audit"]
                == proof["new_model_trials_by_archive"] == 0,
                "cohort execution/original scope differs")
        # The first DeepSeek HIP packet predates this optional archival field.
        # Its absence is not interpreted as a recorded zero-check assertion.
        require("fresh_lean_checks_by_archive" not in proof
                or (type(proof["fresh_lean_checks_by_archive"]) is int
                    and proof["fresh_lean_checks_by_archive"] == 0),
                "archival execution scope differs")
        require([case["case"] for case in raw["cases"]] == CASES
                and [case["case"] for case in summary["cases"]] == CASES
                and raw["selected_cases"] == audit["selected_cases"]
                == audit["replayed_cases"] == CASES
                and row["cases"] == summary["cases"], "case roster/summary differs")
        accepted, requests, all_checks, first_response, first_check = [], [], 0, 0, 0
        for case, case_summary in zip(raw["cases"], summary["cases"], strict=True):
            calls = case["calls"]
            require(case["test_stub"] is False and case["new_source_certificates"] == 0
                    and all(call["test_stub"] is False for call in calls),
                    "case stub/execution scope differs")
            statuses = Counter(call["status"] for call in calls)
            candidates = [call for call in calls if call["status"] in ("unproved", "verified-proof")]
            require(1 <= len(calls) <= 16 and len(candidates) <= 3
                    and statuses["library-read"] <= 8 and set(statuses) <= {
                        "library-read", "no-proof-content", "invalid-proposal", "unproved", "verified-proof"}
                    and [call["request"] for call in calls] == list(range(1, len(calls) + 1)),
                    "case call order/budget differs")
            verified = case["status"] == "verified-proof"
            require(case["status"] in ("verified-proof", "budget-exhausted")
                    and verified == (calls[-1]["status"] == "verified-proof")
                    and not any(call["status"] == "verified-proof" for call in calls[:-1])
                    and (verified or len(calls) == 16 or len(candidates) == 3),
                    "case completion/budget differs")
            first_response += calls[0]["status"] == "verified-proof"
            first_check += bool(candidates) and candidates[0]["status"] == "verified-proof"
            require(case_summary["status"] == case["status"]
                    and case_summary["model_requests"] == len(calls)
                    and case_summary["actual_lean_checks"] == case["proof_checks"] == len(candidates)
                    and case_summary["library_reads"] == case["library_reads"] == statuses["library-read"]
                    and case_summary["call_status_counts"] == dict(statuses)
                    and case_summary["first_response_verified"] is (calls[0]["status"] == "verified-proof")
                    and case_summary["first_actual_lean_check_verified"] is (
                        bool(candidates) and candidates[0]["status"] == "verified-proof"),
                    "case counters/first-attempt metrics differ")
            all_checks += len(candidates)
            requests += [f"cases/{case['case']}/call-{call['request']:02d}/model" for call in calls]
            if verified:
                accepted.append((case["case"], len(calls)))
        fresh = []
        for case, call in accepted:
            main = f"cases/{case}/call-{call:02d}/proof-check/Main.lean"
            for number in (1, 2):
                folder = f"protocol-replay/{case}/call-{call:02d}/fresh-kernel-{number}"
                require(checks[folder + "/Main.lean"] == files[main]
                        and checks[folder + "/lean.log"] != digest(b""),
                        "recorded accepted-Main replay binding differs")
                fresh.append(folder)
        counts = {"cases": 17, "verified_within_budget": len(accepted),
                  "budget_exhausted": 17 - len(accepted), "first_response_verified": first_response,
                  "first_actual_lean_check_verified": first_check, "actual_lean_checks": all_checks,
                  "model_requests": len(requests), "response_files": len(requests),
                  "raw_files": len(files), "audit_files": len(checks),
                  "additional_fresh_kernel_checks": len(fresh)}
        require(all(type(value) is int for value in summary["counts"].values())
                and all(type(value) is int for value in row["recorded_counts"].values())
                and summary["counts"] == row["recorded_counts"] == counts
                and audit["fresh_accepted_proof_kernel_checks"] == fresh
                and audit["bound_model_requests"] == requests
                and audit["recorded_verified_model_proofs"]
                == audit["freshly_verified_model_proofs"] == len(accepted)
                and raw["request_attempts"] == raw["response_files"] == len(requests),
                "cohort/replay counters differ")
        require(proof["raw_results_sha256"] == audit["recording_results_sha256"]
                == digest(content(packet + "/raw-results.json"))
                and proof["audit_results_sha256"] == digest(content(packet + "/audit-results.json"))
                and proof["all_model_requests_bound_to_fixed_protocol"] is True
                and proof["accepted_raw_tactics_bound_to_both_original_and_fresh_Mains"] is True
                and proof["failed_lean_candidates_freshly_rechecked"]
                is audit["failed_candidates_freshly_rechecked"] is False,
                "recorded proof/protocol binding differs")
        cohort_usage = summed([case["reported_usage"] for case in summary["cases"]])
        require(cohort_usage == usage(summary["reported_usage"]) == usage(raw["reported_usage"])
                == usage(audit["reported_usage"]) == usage(row["cohort_reported_usage"]),
                "cohort usage reconciliation differs")
        require(row["levels"] == {"level1": levels(summary["cases"][:12]),
                                  "level2": levels(summary["cases"][12:])},
                "successful-task token means/denominators differ")
        records.append({"packet_path": packet, "manifest_sha256": expected["manifest_sha256"],
                        "raw_files": len(files), "audit_files": len(checks),
                        "response_usage_records": len(requests),
                        "recorded_additional_fresh_kernel_checks": len(fresh)})
        outcomes.append({"model": key[0], "source_language": language, "counts": counts,
                         "reported_usage": cohort_usage, "levels": row["levels"]})
        totals.append(cohort_usage)
    missing = [{"model": model, "source_language": language} for model in MODELS
               for language in ("hip", "cuda") if (model, language) not in keys]
    require(report["missing_cohorts"] == missing
            and report["all_six_independent_cohorts_present"] is (not missing)
            and report["status"] == ("partial-independent-full-size-comparison" if missing
                                     else "six-independent-full-size-cohorts-compared"),
            "complete/missing cohort roster differs")
    require(binding["inputs"] == records and binding["complete_independent_cohorts"] == count
            and binding["missing_cohorts"] == len(missing)
            and binding["input_response_usage_records_checked"]
            == sum(record["response_usage_records"] for record in records)
            and binding["input_raw_files_checked"] == sum(record["raw_files"] for record in records)
            and binding["input_audit_files_checked"] == sum(record["audit_files"] for record in records)
            and binding["recorded_additional_fresh_kernel_checks"]
            == sum(record["recorded_additional_fresh_kernel_checks"] for record in records),
            "comparison aggregate binding differs")
    return {"complete_independent_cohorts": count, "missing_independent_cohorts": missing,
            "all_six_independent_cohorts_present": not missing, "cohorts": outcomes,
            "all_task_reported_usage": summed(totals), "fresh_experiments_by_ledger": False,
            "original_paper_fully_reproduced": False,
            "scope": "Frozen summary, inventory-hash, metric and recorded replay consistency. "
                     "Raw requests/responses, full protocol regeneration, proof executions and "
                     "their stricter validators remain in the linked cohort packets. "
                     "Fixed-scaffold outcomes are separate from original-paper results; "
                     "Level-2 attention is dense SDPA, and CUDA names source language, "
                     "not NVIDIA execution."}
