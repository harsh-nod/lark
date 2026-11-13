"""Replay recorded full-size model protocol decisions without network/model calls.

This binds every replayed prompt, library read and submitted Main to the frozen
task. Recorded failed Lean checks remain recorded failures, not fresh proofs of
failure. Optional accepted-proof rechecks invoke the real parser and Lean kernel.
Captured Python is treated as data and is never imported or executed.
"""

import argparse
import io
import json
from pathlib import Path
import shutil
import sys
from types import SimpleNamespace
import urllib.error
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import certificate, real_backend  # noqa: E402
from lark_kernels.proof_syntax import check_terms  # noqa: E402
from reproduction.local_models import full_shape_run as run  # noqa: E402

RUNNERS = {
    "f3ed2e693ec1f04f17fe52c82e14d71975bd11f7868a8b48339b2bcb7a53b172": {"hip"},
    "0e49b6ce519a2af91c81ee60419adcf37357a71fdf904a772dab0cd279368aef": {"hip"},
    "05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1": {"hip", "cuda"},
}
require = run.require


def read(path):
    return json.loads(path.read_text())


def without_times(value):
    if isinstance(value, list):
        return [without_times(x) for x in value]
    if isinstance(value, dict):
        return {k: without_times(v) for k, v in value.items() if k != "elapsed_seconds"}
    return value


def audit(recording, prepared, output, lean=None, require_full=False):
    recording, prepared, output = (Path(x).resolve() for x in (recording, prepared, output))
    require(not output.exists(), "Audit output must be fresh")
    require(not any(p.is_symlink() for p in recording.rglob("*")), "Recording contains symlinks")
    sources = run.verify_preparation(prepared)
    preparation_sha = run.sha(prepared / "manifest.json")
    language = run.PREPARATIONS[preparation_sha]
    report = read(recording / "results.json")
    require(report["runner_sha256"] in RUNNERS
            and run.sha(recording / "runner.py") == report["runner_sha256"],
            "Unknown or changed recorded controller")
    require(language in RUNNERS[report["runner_sha256"]],
            "Recorded controller does not support this source language")
    require(report["client_sha256"] == run.sha(Path(run.client.__file__))
            == run.sha(recording / "client.py"), "Recorded client differs")
    dependencies = {"full_shape.py", "checkpoint.py"}
    if language == "cuda":
        dependencies.add("cuda_shape.py")
    for name, digest in report["runner_source_sha256"].items():
        require(name in dependencies
                and run.sha(recording / "runner-sources" / name) == digest
                == run.sha(Path(run.__file__).with_name(name)), "Runner dependency differs")
    require(set(report["runner_source_sha256"]) == dependencies,
            "Runner dependency inventory differs")
    require(report["protocol"] == run.PROTOCOL and report["test_stub"] is False,
            "Protocol differs or recording is a test stub")
    require(report["status"] in {"finished", "runtime-uncertain", "infrastructure-error"},
            "A live recording cannot be frozen as completed evidence")
    require(report["preparation_manifest_sha256"] == preparation_sha
            and report.get("source_language", "hip") == language
            and report["external_api_spend_usd"] == report["new_source_certificates"]
            == report["gpu_trials"] == 0 and report["original_paper_fully_reproduced"] is False,
            "Unsupported result scope")
    server = read(recording / "server.json")
    require(run.sha(recording / "server.json") == report["server_record_sha256"]
            and server["status"] == "ready" and server["image"] == run.IMAGE
            and server["model"] == report["model"]
            and server["revision"] == report["revision"] == run.MODELS[report["model"]]
            and len(server["container_id"]) == 64 and not server.get("test_stub", False)
            and server["max_model_len"] >= run.PROTOCOL["context_limit"],
            "Pinned server identity differs")
    run.client.endpoint(server["endpoint"])
    roster = [case[0] for case in run.full_shape.benchmark.CASES]
    selected = report["selected_cases"]
    require(selected and selected == [n for n in roster if n in selected],
            "Selected case order or uniqueness differs")
    cases = report["cases"]
    require([c["case"] for c in cases] == selected[:len(cases)], "Case results are not a prefix")
    if report["status"] == "finished":
        require(len(cases) == len(selected), "Finished recording has missing cases")
    complete = run.cohort_complete(report)
    require(report["complete_17_case_cohort"] is complete, "Full-cohort completion claim differs")
    if "planned_17_case_cohort" in report:
        require(report["planned_17_case_cohort"] is (selected == roster),
                "Planned cohort scope differs")
    if require_full:
        require(complete, "A complete seventeen-case cohort is required")
    require({p.name for p in (recording / "cases").iterdir()} == {c["case"] for c in cases},
            "Unaccounted case directory")
    output.mkdir(parents=True)
    replay = output / "protocol-replay"
    replay.mkdir()
    original_lean = certificate.run_lean
    winners = []
    checked_requests = []
    violations = []

    def guarded(function):
        # The controller intentionally catches model/transport exceptions. A
        # recording-validation failure must still refuse the entire audit, even
        # if somebody relabels that failure as a historical transport outcome.
        def invoke(*args, **kwargs):
            try:
                return function(*args, **kwargs)
            except Exception as error:
                if not getattr(error, "recorded_transport_outcome", False):
                    violations.append(str(error))
                raise
        return invoke

    for case in cases:
        name = case["case"]
        original = recording / "cases" / name
        require(read(original / "results.json") == case, "Case/root report disagreement")
        calls = case["calls"]
        require([c["request"] for c in calls] == list(range(1, len(calls) + 1)),
                "Nonconsecutive request roster")
        require({p.name for p in original.glob("call-*")} ==
                {f"call-{i:02d}" for i in range(1, len(calls) + 1)}, "Unaccounted call directory")
        target = replay / name

        def source_path(destination):
            return original / Path(destination).relative_to(target)

        def recorded_error(folder, row):
            if "http_status" in row:
                body = (folder / "http-error-body.bin").read_bytes()
                require(run.sha(folder / "http-error-body.bin") == row["http_error_body_sha256"],
                        "HTTP error body differs")
                prefix = f"HTTP Error {row['http_status']}: "
                reason = row["error"].removeprefix(prefix)
                error = urllib.error.HTTPError(server["endpoint"], row["http_status"],
                                               reason, None, io.BytesIO(body))
            else:
                error = ValueError(row["error"])
            error.recorded_transport_outcome = True
            raise error

        def recorded_tokenize(url, model, prompt, destination):
            folder = source_path(destination)
            expected = {"model": model, "messages": prompt, "add_generation_prompt": True}
            require(read(folder / "request.json") == expected, "Recorded tokenizer prompt differs")
            if not (folder / "response.json").exists():
                row = calls[int(folder.parent.name.split("-")[1]) - 1]
                recorded_error(folder.parent, row)
            receipt = read(folder / "receipt.json")
            response = read(folder / "response.json")
            require(receipt["request_sha256"] == run.sha(folder / "request.json")
                    and receipt["response_sha256"] == run.sha(folder / "response.json")
                    and receipt["model_inference_calls"] == 0
                    and receipt["input_tokens"] == response["count"] == len(response["tokens"])
                    and receipt["reported_context"] == response["max_model_len"],
                    "Tokenizer receipt differs")
            return response["count"], response["max_model_len"]

        def recorded_call(url, model, messages, destination, **options):
            folder = source_path(destination)
            require(url == server["endpoint"] and model == server["model"],
                    "Replay endpoint/model differs")
            require(options == {"seed": run.PROTOCOL["seed"], "temperature": 0,
                "max_tokens": run.PROTOCOL["max_tokens"],
                "timeout": run.PROTOCOL["model_timeout_seconds"], "reasoning_effort": "low",
                "thinking_token_budget": run.PROTOCOL["thinking_token_budget"]},
                "Replay model-call parameters differ")
            body = {"model": model, "messages": messages, "temperature": 0,
                    "max_tokens": options["max_tokens"], "seed": options["seed"], "stream": False}
            if model.startswith("zai-org/"):
                body["reasoning_effort"] = "low"
            body["thinking_token_budget"] = options["thinking_token_budget"]
            require(read(folder / "request.json") == body, "Model prompt or parameters differ")
            receipt = read(folder / "receipt.json")
            require(receipt["request_sha256"] == run.sha(folder / "request.json")
                    and receipt["endpoint"] == url and receipt["model"] == model
                    and receipt["backend"] == "loopback-vllm"
                    and receipt["external_api_spend_usd"] == 0, "Model request receipt differs")
            checked_requests.append(str(folder.relative_to(recording)))
            row = calls[int(folder.parent.name.split("-")[1]) - 1]
            if not (folder / "response.json").exists():
                recorded_error(folder.parent, row)
            response = read(folder / "response.json")
            require(receipt["response_sha256"] == run.sha(folder / "response.json")
                    and receipt["usage"] == response.get("usage"), "Response/usage receipt differs")
            if receipt["status"] == "error" and receipt.get("error") != "Model produced no proof content":
                recorded_error(folder.parent, row)
            require(response["model"] == model
                    and receipt["finish_reason"] == response["choices"][0].get("finish_reason"),
                    "Response family or finish reason differs")
            content = response["choices"][0]["message"].get("content")
            if not isinstance(content, str) or not content.strip():
                require(receipt["status"] == "error"
                        and receipt["error"] == "Model produced no proof content",
                        "Missing-content outcome differs")
                Path(destination).mkdir()
                shutil.copyfile(folder / "receipt.json", Path(destination) / "receipt.json")
                error = ValueError("Model produced no proof content")
                error.recorded_transport_outcome = True
                raise error
            require(receipt["status"] == "received", "Successful response marked as error")
            return content

        def recorded_syntax(proofs, binary, timeout, **kwargs):
            # run_case calls this immediately after writing action.json.
            pending = sorted(target.glob("call-*/action.json"))[-1].parent
            folder = source_path(pending)
            row = calls[int(folder.name.split("-")[1]) - 1]
            require(read(folder / "action.json") == {"proofs": proofs}, "Recorded proof action differs")
            log = (folder / "proof-syntax.log").read_text()
            accepted = row["proof_syntax_accepted"]
            if accepted:
                require(log.strip() == "LARK_PROOF_TERMS_OK 4", "Syntax audit differs")
            return accepted, log

        def recorded_lean(destination, binary, timeout, **kwargs):
            folder = source_path(destination)
            row = calls[int(folder.parent.name.split("-")[1]) - 1]
            require(timeout == 180 and (Path(destination) / "Main.lean").read_bytes()
                    == (folder / "Main.lean").read_bytes(), "Model-to-Main binding differs")
            require(run.sha(folder / "Main.lean") == row["main_sha256"], "Main digest differs")
            log = (folder / "lean.log").read_text()
            key = "recheck_log_sha256" if folder.name == "independent-recheck" else "lean_log_sha256"
            require(run.sha(folder / "lean.log") == row[key], "Lean log digest differs")
            ok = row["status"] == "verified-proof" or (
                row["status"] == "independent-recheck-failed" and folder.name == "proof-check")
            if ok:
                # Audit recorded diagnostics through the ordinary six-axiom-log gate.
                fake_process = SimpleNamespace(returncode=0, stdout=log, stderr="")
                with patch.object(certificate.subprocess, "run", return_value=fake_process):
                    accepted, _ = original_lean(Path(destination), binary, timeout)
                require(accepted, "Successful recorded Lean log fails the six-axiom gate")
            return ok, log

        args = SimpleNamespace(prepared=prepared, url=server["endpoint"], server=server,
                               model=server["model"], lean="recorded-only", allow_test_stub=False,
                               source_language=language, preparation_manifest_sha256=preparation_sha)
        with patch.object(run, "tokenize", side_effect=guarded(recorded_tokenize)), \
             patch.object(run.client, "call", side_effect=guarded(recorded_call)), \
             patch.object(run, "check_terms", side_effect=guarded(recorded_syntax)), \
             patch.object(run.certificate, "run_lean", side_effect=guarded(recorded_lean)):
            reproduced = run.run_case(name, args, sources, {}, target)
        require(not violations, "Recording protocol refused: " + "; ".join(violations))
        require(without_times(reproduced) == without_times(case), "Replayed case outcome differs")
        for filename in ("fixed-request.json", "library-catalogue.json"):
            require((target / filename).read_bytes() == (original / filename).read_bytes(),
                    "Fixed task or allowed library catalogue differs")
        for candidate in target.glob("call-*/action.json"):
            require(candidate.read_bytes() == source_path(candidate).read_bytes(),
                    "Parsed response action differs")
        for excerpt in target.glob("call-*/library-read.json"):
            require(excerpt.read_bytes() == source_path(excerpt).read_bytes(),
                    "Recorded library excerpt differs from the allowed source")
        if case["status"] == "verified-proof":
            winners.append(target / f"call-{calls[-1]['request']:02d}")

    totals = run.usage(recording)
    require(all(report[k] == value for k, value in totals.items()), "Cohort usage totals differ")
    require(report["model_inference_calls"] == totals["request_attempts"]
            and report["verified_model_proofs"] == len(winners), "Proof/request count differs")
    fresh = []
    if lean and winners:
        libraries = run.full_shape.benchmark.reference_libraries(run.full_shape.references)
        _, environment = real_backend.prepare(libraries, str(lean), 600, target=run.full_shape.TARGET)
        for winner in winners:
            proofs = read(winner / "action.json")["proofs"]
            ok, log = check_terms(proofs, str(lean), 180, env=environment,
                                  imports=(run.full_shape.TARGET,))
            (winner / "fresh-proof-syntax.log").write_text(log)
            require(ok, "Fresh parser refused an accepted model proof")
            for number in (1, 2):
                folder = winner / f"fresh-kernel-{number}"
                folder.mkdir()
                shutil.copyfile(winner / "proof-check/Main.lean", folder / "Main.lean")
                ok, log = original_lean(folder, str(lean), 180, env=environment)
                (folder / "lean.log").write_text(log)
                require(ok, "Fresh accepted-proof kernel/axiom recheck failed")
                fresh.append(str(folder.relative_to(output)))
    result = {"schema": 1, "status": "recorded-full-size-protocol-replayed",
              "recording_results_sha256": run.sha(recording / "results.json"),
              "preparation_manifest_sha256": preparation_sha, "source_language": language,
              "controller_sha256": run.sha(Path(run.__file__)),
              "auditor_sha256": run.sha(Path(__file__)), "model": report["model"],
              "selected_cases": selected, "replayed_cases": [c["case"] for c in cases],
              "complete_17_case_cohort": complete, "bound_model_requests": checked_requests,
              "reported_usage": totals["reported_usage"],
              "recorded_verified_model_proofs": len(winners),
              "freshly_verified_model_proofs": len(winners) if lean else 0,
              "fresh_accepted_proof_kernel_checks": fresh,
              "failed_candidates_freshly_rechecked": False, "model_calls_by_audit": 0,
              "external_api_spend_usd": 0, "new_registered_source_certificates": 0,
              "original_paper_fully_reproduced": False}
    run.write(output / "results.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("recording", "prepared", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--lean", type=Path, help="Fresh parser and two kernel checks per accepted proof")
    parser.add_argument("--require-full-cohort", action="store_true")
    args = parser.parse_args()
    result = audit(args.recording, args.prepared, args.output, args.lean, args.require_full_cohort)
    print(json.dumps({k: result[k] for k in ("status", "complete_17_case_cohort",
                     "recorded_verified_model_proofs", "freshly_verified_model_proofs",
                     "model_calls_by_audit")}))


if __name__ == "__main__":
    main()
