"""Recorded offline model experiments on the frozen seventeen full-size tasks.

Only bounded library reads and four tactic bodies are accepted. Models cannot
read SDK renderers or the positive-control solutions. Proof success requires
two fresh Lean invocations with all six standard axiom audits.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import sys
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import certificate, real_backend  # noqa: E402
from lark_kernels.proof_syntax import check_terms  # noqa: E402
from reproduction.local_models import client, full_shape  # noqa: E402
from reproduction.local_models.checkpoint import MODELS  # noqa: E402
from reproduction.specification_validation.study import owned_sources  # noqa: E402

PREPARATION_SHA256 = "82f84eec835c0deb27e618ddd6e3d75d9b1d3b8827bd1a4f1982de0d4e029db8"
CUDA_PREPARATION_SHA256 = "6476ec66614e412a122654036b6bd66fab67b23007d7fc26181cdff7571f34c2"
PREPARATIONS = {PREPARATION_SHA256: "hip", CUDA_PREPARATION_SHA256: "cuda"}
IMAGE = (
    "vllm/vllm-openai-rocm@sha256:71a5d125b10a594752014b917a00cb1743387d1be9ee188aa1862af0b143c7dd"
)
PROTOCOL = {
    "version": "full-shape-bounded-library-reads-v1",
    "request_budget": 16,
    "proof_check_budget": 3,
    "library_read_budget": 8,
    "max_read_lines": 120,
    "max_tokens": 16384,
    "thinking_token_budget": 4096,
    "seed": 261102028,
    "temperature": 0,
    "reasoning_effort": "low",
    "context_limit": 65536,
    "context_margin": 256,
    "model_timeout_seconds": 1800,
    "lean_timeout_seconds": 180,
    "feedback_chars": 12000,
    "last_response_chars": 8000,
}
TARGETS = {
    **{n: "Lark.Pointwise" for n in ("relu", "silu", "gelu")},
    **{n: "Lark.Normalization" for n in ("rmsnorm", "layernorm", "softmax")},
    "gemv": "Lark.DotLoop",
    "gemm": "Lark.Matrix",
    "bmm": "Lark.Matrix",
    "linear": "Lark.Bias",
    "conv2d": "Lark.Convolution",
    "depthwise_conv": "Lark.Convolution",
    "rope": "Lark.Rotary",
    "ffn": "Lark.FeedForward",
    "swiglu": "Lark.SwiGLU",
    "attention": "Lark.AttentionPipeline",
    "gqa": "Lark.AttentionPipeline",
}
SYSTEM = """Prove the four fixed Lean 4.19.0 theorem slots for this full-size GPU task.
The program, task, reference, theorem statements, final theorem assembly and limits
are immutable. All scalar operations are arbitrary; do not assume algebraic laws.
You may inspect only the listed generic Lean libraries through bounded reads.
Return exactly one JSON object in one of these two forms:
{"read_library":{"path":"Lark/Pointwise.lean","start_line":1,"line_count":80}}
{"proofs":{"segmentation_data":"by ...","segmentation":"by ...","race_free":"by ...","segment_equivalence":"by ..."}}
There are at most 16 responses, 8 library reads and 3 candidate Lean checks.
Each read contains at most 120 lines. Each proof must start with by and use at
most 20000 characters. No comments, declarations, sorry, admit, axioms,
native_decide, run_tac, metaprogramming, IO, option changes or shell commands.
Lean checks every candidate independently. Use the feedback to revise proofs.
The SDK's concrete positive-control solutions are unavailable. Return JSON only.
"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write(path, value):
    path.write_bytes(encoded(value))


def safe_file(root, name):
    path = PurePosixPath(name)
    require(
        path.parts and not path.is_absolute() and ".." not in path.parts and str(path) == name,
        "Unsafe fixture path",
    )
    result = root / name
    require(not result.is_symlink() and result.resolve().is_relative_to(root), "Fixture symlink")
    return result


def verify_preparation(root):
    manifest_sha = sha(root / "manifest.json")
    require(manifest_sha in PREPARATIONS, "Unrecognized frozen preparation")
    manifest = json.loads((root / "manifest.json").read_text())
    require(
        {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
        == set(manifest) | {"manifest.json"},
        "Unexpected preparation files",
    )
    for name, expected in manifest.items():
        require(sha(safe_file(root, name)) == expected, "Changed preparation file: " + name)
    sources = json.loads((root / "source-manifest.json").read_text())
    synthetic = "lean-real/LarkReal/BenchmarkReferenceImports.lean"
    for name, expected in sources.items():
        if name == synthetic:
            actual = ROOT / "reproduction/benchmark_specification_validation/BenchmarkImports.lean"
        else:
            actual = safe_file(ROOT, name)
        require(
            sha(actual) == expected,
            "Current SDK/reference differs from frozen preparation: " + name,
        )
    report = json.loads((root / "results.json").read_text())
    require(
        report["status"] == "full-shape-model-fixtures-prepared-and-baselines-checked"
        and report["positive_lean_checks"] == report["masked_negative_lean_checks"] == 17
        and report.get("language", "hip") == PREPARATIONS[manifest_sha],
        "Incomplete preparation",
    )
    return sources


def library_context(case, sources):
    libraries = owned_sources(TARGETS[case])
    catalogue = {}
    for name, content in libraries.items():
        prefix = "lean-real/" if name.startswith("LarkReal/") else "lean/"
        require(
            hashlib.sha256(content).hexdigest() == sources[prefix + name], "Library source differs"
        )
        lines = content.decode().splitlines()
        declarations = []
        for i, line in enumerate(lines, 1):
            if re.match(
                r"^(?:@\[[^\]]+\]\s*)?(?:(?:private|protected|noncomputable|partial) )*"
                r"(?:def|theorem|lemma|abbrev|structure|inductive|instance|namespace)\b",
                line,
            ):
                declarations.append({"line": i, "header": line[:240]})
        catalogue[name] = {
            "sha256": hashlib.sha256(content).hexdigest(),
            "lines": len(lines),
            "declarations": declarations,
        }
    return libraries, catalogue


def read_library(action, libraries):
    require(
        isinstance(action, dict) and set(action) == {"path", "start_line", "line_count"},
        "Library read requires path, start_line and line_count only",
    )
    path, start, count = action["path"], action["start_line"], action["line_count"]
    require(
        isinstance(path, str) and path in libraries,
        "Library path is outside the allowed source set",
    )
    require(
        type(start) is int and type(count) is int and 1 <= count <= PROTOCOL["max_read_lines"],
        "Library read must request 1..120 lines",
    )
    lines = libraries[path].decode().splitlines()
    require(1 <= start <= len(lines), "Library start line is out of range")
    end = min(start + count - 1, len(lines))
    return {
        "path": path,
        "start_line": start,
        "end_line": end,
        "source_sha256": hashlib.sha256(libraries[path]).hexdigest(),
        "text": "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1)),
    }


def parse_action(content):
    text = content.strip()
    if text.startswith("```"):
        text = text.split("\n", 1)[1].rsplit("```", 1)[0].strip()

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "Duplicate JSON object key")
            result[key] = value
        return result

    value = json.loads(text, object_pairs_hook=unique_object)
    require(
        isinstance(value, dict)
        and len(value) == 1
        and set(value) in ({"read_library"}, {"proofs"}),
        "Return one library read or four proofs",
    )
    if "proofs" in value:
        full_shape.validate_proofs(value["proofs"])
    return value


def messages(request, catalogue, excerpts, feedback, last_response, remaining):
    state = {"fixed_task": request, "library_catalogue": catalogue, "remaining": remaining}
    user = "Fixed task and library index:\n" + json.dumps(state, ensure_ascii=False)
    for excerpt in excerpts:
        user += (
            "\nLibrary "
            + excerpt["path"]
            + " lines "
            + str(excerpt["start_line"])
            + ".."
            + str(excerpt["end_line"])
            + "\n"
            + excerpt["text"]
            + "\n"
        )
    user += "\nPrevious response (bounded):\n" + last_response[: PROTOCOL["last_response_chars"]]
    user += "\nChecker/protocol feedback (bounded):\n" + feedback[: PROTOCOL["feedback_chars"]]
    return [{"role": "system", "content": SYSTEM}, {"role": "user", "content": user}]


def tokenize(url, model, prompt, output):
    client.endpoint(url)
    body = {"model": model, "messages": prompt, "add_generation_prompt": True}
    data = encoded(body)
    (output / "request.json").write_bytes(data)
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), client.NoRedirect())
    request = urllib.request.Request(
        url.removesuffix("/v1/chat/completions") + "/tokenize",
        data=data,
        headers={"Content-Type": "application/json"},
    )
    with opener.open(request, timeout=30) as response:
        raw = response.read(8 * 1024 * 1024 + 1)
    require(len(raw) <= 8 * 1024 * 1024, "Oversized tokenization response")
    (output / "response.json").write_bytes(raw)
    result = json.loads(raw)
    require(
        type(result.get("count")) is int
        and result["count"] >= 0
        and type(result.get("max_model_len")) is int
        and result["max_model_len"] > 0
        and isinstance(result.get("tokens"), list)
        and len(result["tokens"]) == result["count"],
        "Invalid tokenizer count/context",
    )
    write(
        output / "receipt.json",
        {
            "status": "tokenized",
            "input_tokens": result["count"],
            "reported_context": result["max_model_len"],
            "request_sha256": hashlib.sha256(data).hexdigest(),
            "response_sha256": hashlib.sha256(raw).hexdigest(),
            "model_inference_calls": 0,
            "scope": "Conservative chat-template context preflight; actual inference usage remains authoritative.",
        },
    )
    return result["count"], result["max_model_len"]


def fit_messages(args, request, catalogue, excerpts, feedback, last_response, remaining, folder):
    excerpts = list(excerpts)
    compactions = []
    for i in range(PROTOCOL["library_read_budget"] + 4):
        prompt = messages(request, catalogue, excerpts, feedback, last_response, remaining)
        destination = folder / f"tokenize-{i:02d}"
        destination.mkdir()
        count, context = tokenize(args.url, args.model, prompt, destination)
        limit = min(PROTOCOL["context_limit"], context, args.server["max_model_len"])
        if count + PROTOCOL["max_tokens"] + PROTOCOL["context_margin"] <= limit:
            return prompt, excerpts, compactions
        if excerpts:
            removed = excerpts.pop(0)
            compactions.append(
                {"dropped_oldest_excerpt": {k: v for k, v in removed.items() if k != "text"}}
            )
        elif len(feedback) > 2000:
            feedback = feedback[:2000]
            compactions.append({"feedback_reduced_to_chars": 2000})
        elif last_response:
            last_response = ""
            compactions.append({"previous_response_omitted": True})
        else:
            raise ValueError("Immutable task and library index exceed the fixed context budget")
    raise ValueError("Context compaction exhausted without changing the immutable task")


def run_case(case, args, sources, environment, folder):
    folder.mkdir()
    original = args.prepared / "cases" / case
    request = json.loads((original / "request.json").read_text())
    require(request.get("language", "hip") == getattr(args, "source_language", "hip"),
            "Task language differs from the pinned preparation")
    block = (original / "sdk-block.lean.txt").read_text()
    masked = {n: "by fail" for n in full_shape.SLOTS}
    require(
        full_shape.render(block, masked) == request["immutable_main"],
        "Masked request differs from fixed declarations",
    )
    libraries, catalogue = library_context(case, sources)
    write(folder / "fixed-request.json", request)
    write(folder / "library-catalogue.json", catalogue)
    result = {
        "case": case,
        "status": "in-progress",
        "calls": [],
        "proof_checks": 0,
        "library_reads": 0,
        "test_stub": args.allow_test_stub,
        "new_source_certificates": 0,
        "syntax_checks": 0,
        "preparation_manifest_sha256": getattr(args, "preparation_manifest_sha256", PREPARATION_SHA256),
        "fixed_request_sha256": sha(original / "request.json"),
    }
    feedback = (
        "No candidate yet. Inspect generic libraries as needed and prove all four fixed goals."
    )
    excerpts, last_response = [], ""
    write(folder / "results.json", result)
    for i in range(1, PROTOCOL["request_budget"] + 1):
        if result["proof_checks"] >= PROTOCOL["proof_check_budget"]:
            break
        destination = folder / f"call-{i:02d}"
        destination.mkdir()
        row = {"request": i, "test_stub": args.allow_test_stub}
        started = time.monotonic()
        remaining = {
            "model_requests": PROTOCOL["request_budget"] - i + 1,
            "proof_checks": PROTOCOL["proof_check_budget"] - result["proof_checks"],
            "library_reads": PROTOCOL["library_read_budget"] - result["library_reads"],
        }
        try:
            prompt, excerpts, compactions = fit_messages(
                args, request, catalogue, excerpts, feedback, last_response, remaining, destination
            )
            row["context_compactions"] = compactions
            row["messages_sha256"] = hashlib.sha256(encoded(prompt)).hexdigest()
            content = client.call(
                args.url,
                args.model,
                prompt,
                destination / "model",
                seed=PROTOCOL["seed"],
                temperature=0,
                max_tokens=PROTOCOL["max_tokens"],
                timeout=PROTOCOL["model_timeout_seconds"],
                reasoning_effort="low",
                thinking_token_budget=PROTOCOL["thinking_token_budget"],
            )
        except Exception as error:
            if isinstance(error, urllib.error.HTTPError):
                row["http_status"] = error.code
                try:
                    body = error.read(1024 * 1024)
                    (destination / "http-error-body.bin").write_bytes(body)
                    row["http_error_body_sha256"] = hashlib.sha256(body).hexdigest()
                except Exception as body_error:
                    row["http_error_body_read_error"] = str(body_error)
            receipt = destination / "model/receipt.json"
            no_content = receipt.is_file() and str(error) == "Model produced no proof content"
            row.update(
                status="no-proof-content" if no_content else "runtime-or-context-error",
                error=str(error),
                elapsed_seconds=time.monotonic() - started,
            )
            if not no_content:
                result["status"] = "runtime-uncertain"
            result["calls"].append(row)
            write(folder / "results.json", result)
            print(json.dumps({"case": case, **row}), flush=True)
            if no_content:
                feedback = "The previous response had no final content. Return a library read or four concise proofs as JSON."
                continue
            break
        last_response = content
        try:
            action = parse_action(content)
            write(destination / "action.json", action)
            if "read_library" in action:
                require(
                    result["library_reads"] < PROTOCOL["library_read_budget"],
                    "Library read budget is exhausted",
                )
                excerpt = read_library(action["read_library"], libraries)
                write(destination / "library-read.json", excerpt)
                excerpts.append(excerpt)
                result["library_reads"] += 1
                row["status"] = "library-read"
                feedback = "The requested source excerpt is included. No proof has been checked for this read."
            else:
                result["syntax_checks"] += 1
                syntax_ok, syntax_log = check_terms(
                    action["proofs"],
                    str(args.lean),
                    180,
                    env=environment,
                    imports=(full_shape.TARGET,),
                )
                (destination / "proof-syntax.log").write_text(syntax_log)
                row["proof_syntax_accepted"] = syntax_ok
                require(
                    syntax_ok,
                    "Proof-term parser refused the candidate; see recorded proof-syntax.log",
                )
                result["proof_checks"] += 1
                check = destination / "proof-check"
                check.mkdir()
                main = full_shape.render(block, action["proofs"])
                (check / "Main.lean").write_text(main)
                ok, log = certificate.run_lean(check, str(args.lean), 180, env=environment)
                (check / "lean.log").write_text(log)
                row.update(
                    status="proved-first-check" if ok else "unproved",
                    main_sha256=sha(check / "Main.lean"),
                    lean_log_sha256=sha(check / "lean.log"),
                    lean_timed_out="Lean timed out" in log,
                )
                feedback = log
                if ok:
                    recheck = destination / "independent-recheck"
                    recheck.mkdir()
                    (recheck / "Main.lean").write_text(main)
                    again, relog = certificate.run_lean(
                        recheck, str(args.lean), 180, env=environment
                    )
                    (recheck / "lean.log").write_text(relog)
                    row["recheck_log_sha256"] = sha(recheck / "lean.log")
                    if again:
                        row["status"] = result["status"] = "verified-proof"
                    else:
                        row["status"] = "independent-recheck-failed"
                        result["status"] = "infrastructure-error"
        except (ValueError, TypeError, KeyError, RecursionError) as error:
            row.update(status="invalid-proposal", error=str(error))
            feedback = "Proposal refused before acceptance: " + str(error)
        row["elapsed_seconds"] = time.monotonic() - started
        result["calls"].append(row)
        write(folder / "results.json", result)
        print(json.dumps({"case": case, **row}), flush=True)
        if result["status"] in ("verified-proof", "infrastructure-error"):
            break
    if result["status"] == "in-progress":
        result["status"] = "budget-exhausted"
    write(folder / "results.json", result)
    return result


def usage(output):
    receipts = [json.loads(p.read_text()) for p in output.glob("cases/*/call-*/model/receipt.json")]
    keys = ("prompt_tokens", "completion_tokens", "total_tokens")
    incomplete = any(
        not isinstance(r.get("usage"), dict)
        or any(type(r["usage"].get(k)) is not int or r["usage"][k] < 0 for k in keys)
        or r["usage"]["prompt_tokens"] + r["usage"]["completion_tokens"]
        != r["usage"]["total_tokens"]
        for r in receipts
    )
    totals = {
        k: sum(
            r["usage"][k]
            for r in receipts
            if isinstance(r.get("usage"), dict) and type(r["usage"].get(k)) is int
        )
        for k in keys
    }
    return {
        "request_attempts": len(receipts),
        "response_files": len(list(output.glob("cases/*/call-*/model/response.json"))),
        "usage_incomplete": incomplete,
        "reported_usage": totals,
    }


def cohort_complete(report):
    expected = [case[0] for case in full_shape.benchmark.CASES]
    return (
        report["status"] == "finished"
        and report["selected_cases"] == expected
        and [case["case"] for case in report["cases"]] == expected
        and all(
            case["status"] in ("verified-proof", "budget-exhausted") for case in report["cases"]
        )
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("prepared", "server-record", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--url", required=True)
    parser.add_argument("--model", required=True, choices=sorted(MODELS))
    parser.add_argument("--case", action="append", choices=list(TARGETS))
    parser.add_argument(
        "--allow-test-stub",
        action="store_true",
        help="Explicit test-only mode; never counted as model inference",
    )
    args = parser.parse_args()
    client.endpoint(args.url)
    args.prepared = args.prepared.resolve()
    args.output = args.output.resolve()
    args.lean = Path(certificate.lean_binary(str(args.lean)))
    sources = verify_preparation(args.prepared)
    args.preparation_manifest_sha256 = sha(args.prepared / "manifest.json")
    args.source_language = PREPARATIONS[args.preparation_manifest_sha256]
    args.server = json.loads(args.server_record.read_text())
    require(
        args.server.get("status") == "ready"
        and args.server.get("model") == args.model
        and args.server.get("endpoint") == args.url
        and type(args.server.get("max_model_len")) is int
        and args.server["max_model_len"] >= PROTOCOL["context_limit"],
        "Server identity/context is incompatible",
    )
    require(
        bool(args.server.get("test_stub", False)) == args.allow_test_stub,
        "Test stubs require explicit test-only mode",
    )
    if not args.allow_test_stub:
        require(
            args.server.get("revision") == MODELS[args.model]
            and args.server.get("image") == IMAGE
            and isinstance(args.server.get("container_id"), str)
            and len(args.server["container_id"]) == 64,
            "Pinned checkpoint/image/container identity is required",
        )
    require(
        not any((p / ".git").exists() for p in (args.output, *args.output.parents)),
        "Run output must be outside Git",
    )
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "cases").mkdir()
    write(args.output / "server.json", args.server)
    shutil.copyfile(Path(__file__), args.output / "runner.py")
    shutil.copyfile(Path(client.__file__), args.output / "client.py")
    captured = args.output / "runner-sources"
    captured.mkdir()
    dependencies = ["full_shape.py", "checkpoint.py"]
    if args.source_language == "cuda":
        dependencies.append("cuda_shape.py")
    for name in dependencies:
        shutil.copyfile(Path(__file__).with_name(name), captured / name)
    selected = [c[0] for c in full_shape.benchmark.CASES if not args.case or c[0] in args.case]
    report = {
        "schema": 1,
        "status": "in-progress",
        "protocol": PROTOCOL,
        "model": args.model,
        "source_language": args.source_language,
        "revision": args.server.get("revision"),
        "selected_cases": selected,
        "planned_17_case_cohort": len(selected) == 17,
        "complete_17_case_cohort": False,
        "test_stub": args.allow_test_stub,
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "runner_sha256": sha(Path(__file__)),
        "client_sha256": sha(Path(client.__file__)),
        "server_record_sha256": sha(args.server_record),
        "preparation_manifest_sha256": args.preparation_manifest_sha256,
        "external_api_spend_usd": 0,
        "new_source_certificates": 0,
        "gpu_trials": 0,
        "original_paper_fully_reproduced": False,
        "cases": [],
        "scope": f"Independent full-size {args.source_language.upper()} proof-slot/library-read experiment. No original registry/harness/stage-cost or historical pass-rate reproduction. SDK controls are not model successes.",
    }
    write(args.output / "results.json", report)
    report["runner_source_sha256"] = {p.name: sha(p) for p in captured.iterdir()}
    try:
        libraries = full_shape.benchmark.reference_libraries(full_shape.references)
        cache, environment = real_backend.prepare(
            libraries, str(args.lean), 600, target=full_shape.TARGET
        )
        write(
            args.output / "imports.json",
            {
                "source_checked_cache": str(cache),
                "checked_build_sha256": sha(cache / "checked-build.json"),
                "cold_import_rebuild_claimed": False,
            },
        )
        for case in selected:
            verify_preparation(args.prepared)
            client.check_health(args.url, args.model)
            result = run_case(case, args, sources, environment, args.output / "cases" / case)
            report["cases"].append(result)
            report.update(usage(args.output))
            report["model_inference_calls"] = (
                0 if args.allow_test_stub else report["request_attempts"]
            )
            write(args.output / "results.json", report)
            if result["status"] in ("runtime-uncertain", "infrastructure-error"):
                report["status"] = result["status"]
                break
        else:
            report["status"] = "finished"
    except Exception as error:
        report.update(status="infrastructure-error", error=str(error))
    report.update(usage(args.output))
    report["model_inference_calls"] = 0 if args.allow_test_stub else report["request_attempts"]
    report["verified_model_proofs"] = (
        0 if args.allow_test_stub else sum(c["status"] == "verified-proof" for c in report["cases"])
    )
    report["complete_17_case_cohort"] = cohort_complete(report)
    write(args.output / "results.json", report)
    print(
        json.dumps(
            {
                k: report[k]
                for k in (
                    "status",
                    "model",
                    "test_stub",
                    "model_inference_calls",
                    "verified_model_proofs",
                )
            }
        )
    )
    if report["status"] != "finished":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
