"""Bind the complete recorded FFN proof to actual source CI and public bytes.

Captured code and compiled objects remain data. This reader adds no Lean,
hardware, model or original-paper result, and counts one FFN pipeline identity.
"""

import json
from pathlib import Path
import re

if __package__:
    from .ptx_ffn_evidence import Recording, same_json, sha
    from .ptx_ffn_packet import Packet
    from .ptx_rotary_release import check_source_ci
else:
    from ptx_ffn_evidence import Recording, same_json, sha
    from ptx_ffn_packet import Packet
    from ptx_rotary_release import check_source_ci

ROOT = Path(__file__).resolve().parents[2]
SPEC_KEYS = ("prefix", "receipt_prefix", "history_prefix", "ci_prefix", "ci_job_prefix",
             "publication_prefix", "ledger_publication_prefix")


def load_protocol():
    return json.loads(Path(__file__).with_name("ptx_ffn_release_protocol.json").read_text())


def check_ci_build(reader, prefix):
    """Check all actual compiler logs retained by the source CI job."""
    proof = reader.read(prefix + "/results.json")
    protocol = reader.protocol
    reader.fields(proof, protocol["positive_fields"], "CI positive proof/resource/input scope differs")
    checks = proof["module_checks"]
    reader.require(type(checks) is list and len(checks) == 14
                   and [r.get("module") for r in checks] == ["Lark." + n for n in protocol["modules"]],
                   "CI fresh module roster differs")
    library = {}
    for name, row in zip(protocol["modules"], checks, strict=True):
        log = reader.content(prefix + "/" + name + ".log")
        reader.check(row, log, ["-o", "Lark/" + name + ".olean", "Lark/" + name + ".lean"])
        library.update(reader.audits(log, protocol["module_audit_names"][name]))
    log = reader.content(prefix + "/Main.log")
    reader.check(proof["main_check"], log, ["Main.lean"])
    main = reader.audits(log, protocol["main_audit_names"])
    reader.require(len(library) == 252 and len(main) == 4
                   and same_json(library, proof["library_axiom_audits"])
                   and same_json(main, proof["axiom_audits"]), "CI actual axiom audits differ")
    for name in ("import_build_seconds", "total_seconds"):
        value = proof[name]
        reader.require(type(value) in (int, float) and 0 <= value <= 600, "CI aggregate build cap differs")
    reader.require(proof["import_build_seconds"] <= proof["total_seconds"], "CI build timing order differs")
    return proof


def check_ci(reader, protocol):
    p = protocol
    ci, job = p["ci_prefix"], p["ci_job_prefix"]
    summary, run, jobs = (reader.read(ci + "/" + n) for n in ("results.json", "run.json", "jobs.json"))
    check_source_ci(reader, summary, run, jobs, p)
    reader.require(summary["observer_sha256"] == sha(reader.content(ci + "/observer.py"))
                   == p["ci_observer_sha256"], "CI observer binding differs")
    actual = reader.read(job + "/job.json")
    reader.fields(actual, {"id": p["ci_matrix_job_id"], "run_id": p["ci_run"],
                  "head_sha": p["published_source"], "name": "ptx-matrix",
                  "status": "completed", "conclusion": "success"}, "actual FFN CI job differs")
    rows = [j for j in jobs["jobs"] if j["id"] == actual["id"]]
    reader.require(len(rows) == 1 and same_json(rows[0], actual), "whole-workflow and FFN job responses differ")
    required = [s for s in actual["steps"] if s["name"] in p["ci_required_steps"]]
    reader.require(len(required) == 5 and {s["name"] for s in required} == set(p["ci_required_steps"])
                   and all(s["status"] == "completed" and s["conclusion"] == "success" for s in required),
                   "actual FFN CI certificate steps differ")
    reader.fields(reader.read(job + "/results.json"), p["ci_job_summary_fields"], "FFN CI job capture differs")
    dumped = {}
    for line in reader.content(job + "/logs.raw").decode().splitlines():
        start = line.find('{"FFN_evidence":')
        if start >= 0:
            row = json.loads(line[start:])
            name = row["FFN_evidence"]
            reader.require(type(name) is str and name not in dumped and type(row["text"]) is str,
                           "CI dump contains duplicate or invalid records")
            dumped[name] = row["text"].encode()
    reader.require(set(dumped) == set(p["ci_dump_files"])
                   and all(reader.content(job + "/dumped-evidence/" + n) == data for n, data in dumped.items()),
                   "actual CI log and captured evidence bytes differ")
    prefix = job + "/dumped-evidence/"
    proofs = [check_ci_build(reader, prefix + name) for name in (
        "lark-ptx-ffn-ci-export", "lark-ptx-ffn-ci-source-controls/positive-source-only-replay")]
    reader.require(same_json([r["total_seconds"] for r in proofs], p["ci_job_summary_fields"]["certificate_build_seconds"]),
                   "CI build-time capture differs")
    direct_prefix = prefix + "lark-ptx-ffn-ci-source-controls"
    direct = reader.read(direct_prefix + "/results.json")
    reader.counters(direct, {"positive_controls": 1, "direct_Lean_negative_controls": 4,
                    "timeouts": 0, "resource_limit_failures": 0, "owned_modules_freshly_compiled": 14,
                    "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
                    "model_calls": 0, "gpu_trials": 0}, "CI direct control counters differ")
    reader.fields(direct, {"status": "all-four-direct-Lean-FFN-controls-rejected",
                  "old_owned_olean_cache_used": False, "nvidia_execution": False,
                  "original_paper_fully_reproduced": False}, "CI direct control scope differs")
    specs = reader.protocol["packet"]["direct_controls"]
    reader.require(type(direct["negative_controls"]) is list and len(direct["negative_controls"]) == 4,
                   "CI direct control roster differs")
    for row, spec in zip(direct["negative_controls"], specs, strict=True):
        reader.fields(row, spec["fields"], "CI direct source/theorem/input binding differs")
        part = direct_prefix + "/" + row["control"]
        reader.require(same_json(row, reader.read(part + "/results.json")), "CI copied direct control differs")
        log = reader.content(part + "/Lean.log")
        reader.check(row["Lean"], log, spec["command"], accepted=False)
        filename = spec["command"][0].encode()
        lines = [int(n) for n in re.findall(re.escape(filename) + rb":([0-9]+):[0-9]+: error:", log)]
        first, last = row["expected_lines"]
        reader.require(any(first <= n <= last for n in lines) and not any(marker in log.lower() for marker in (
            b"stack overflow", b"maximum recursion", b"maximum number of heartbeats", b"deep recursion")),
            "CI direct theorem refusal/resource differs")
    false = reader.read(prefix + "lark-ptx-ffn-ci-recording-controls/results.json")
    reader.counters(false, {"negative_controls": 31, "fresh_Lean_checks": 0, "model_calls": 0, "GPU_trials": 0},
                    "CI false-recording counters differ")
    reader.require([r["name"] for r in false["checks"]] == [r["name"] for r in reader.protocol["packet"]["false_controls"]]
                   and all(r["status"] == "rejected-before-fresh-Lean-work" and r["output_created"] is False
                           and same_json(r, reader.read(prefix + "lark-ptx-ffn-ci-recording-controls/" + r["name"] + "/results.json"))
                           for r in false["checks"]), "CI complete refusal transcript roster differs")
    return 2


def check_downloads(reader, protocol):
    p, prefix = protocol, protocol["publication_prefix"]
    report = reader.read(prefix + "/results.json")
    reader.fields(report, p["publication_fields"], "anonymous FFN publication scope/counters differ")
    reader.require(sha(reader.content(prefix + "/descriptor.json")) == p["publication_descriptor_sha256"]
                   and sha(reader.content(prefix + "/driver.py")) == p["publication_driver_sha256"],
                   "actual anonymous publication descriptor/driver differs")
    descriptor = reader.read(prefix + "/descriptor.json")
    downloads = reader.read(prefix + "/downloads.json")
    reader.require(descriptor["source_commit"] == p["published_source"] and len(downloads) == 34
                   and len(descriptor["files"]) == 34
                   and len({r["path"] for r in downloads}) == 34
                   and {r["path"] for r in downloads} == set(p["publication_files"]),
                   "actual anonymous download roster differs")
    for row in downloads:
        expected = p["publication_files"][row["path"]]
        url = "https://raw.githubusercontent.com/harsh-nod/lark/" + p["published_source"] + "/" + row["path"]
        reader.fields(row, {**expected, "url": url, "final_url": url, "status": "verified",
                      "http_status": 200, "authorization_header": False, "tls_verification": True},
                      "actual anonymous download observation differs")
        data = reader.content(row["path"])
        reader.require(len(data) == expected["bytes"] and sha(data) == expected["sha256"],
                       "actual published FFN file bytes differ")
    reader.require(sum(r["bytes"] for r in downloads) == 289901390,
                   "anonymous FFN downloaded-byte total differs")
    integrity = reader.read(prefix + "/integrity/results.json")
    reader.fields(integrity, {"status": "complete-FFN-publication-payload-integrity-passed",
                  "packet_manifest_sha256": reader.protocol["packet"]["manifest_sha256"],
                  "captured_code_executed": False, "original_paper_fully_reproduced": False},
                  "anonymous integrity reader scope differs")
    reader.counters(integrity, {"archive_members_checked": 4416, "uncompressed_member_bytes_checked": 940266976,
                    "fresh_Lean_checks": 0, "model_calls": 0, "GPU_trials": 0,
                    "new_registered_source_certificates": 0}, "anonymous integrity counters differ")
    return len(downloads)


def check_ptx_ffn_evidence(config, root=ROOT, *, protocol=None):
    root, p = Path(root).resolve(), load_protocol() if protocol is None else protocol
    reader = Recording(root, max_file_bytes=90_000_000)
    declared = {n for group in config["evidence_groups"].values() for n in group}
    reader.require(same_json(config.get("ptx_ffn_proof"), {k: p[k] for k in SPEC_KEYS}),
                   "declared FFN proof paths differ")
    expected_packet = {"manifest.json", "results.json", "packaging-driver.py"}
    for label in reader.protocol["packet"]["archives"]:
        expected_packet.update((label + ".tar.gz", label + "-files.json"))
    reader.require({p["prefix"] + "/" + n for n in expected_packet} <= declared
                   and set(p["retained_files"]) <= declared, "complete FFN evidence must be declared")
    ci_builds, public_files = check_ci(reader, p), check_downloads(reader, p)
    ledger = reader.read(p["ledger_publication_prefix"] + "/results.json")
    reader.fields(ledger, p["ledger_publication_fields"], "source-bound full v27 publication scope differs")
    rows = ledger["downloaded_files"]
    reader.require(len(rows) == 20 and {r["path"] for r in rows} == set(p["ledger_publication_files"]),
                   "source-bound full v27 publication roster differs")
    for row in rows:
        reader.fields(row, {**p["ledger_publication_files"][row["path"]], "http_status": 200,
                      "tls_verification": True, "curl_ssl_verify_result": 0, "authorization_header": False},
                      "source-bound full v27 download observation differs")
    checks = ledger["validation"]["checks"]
    reader.require(len(checks) == 98 and sum(r["accepted"] is True for r in checks) == 9
                   and sum(r["accepted"] is False for r in checks) == 89,
                   "source-bound full v27 complete control outcomes differ")
    # Pin every retained failure/history byte, including earlier timeouts and
    # cancelled CI. Nothing is deleted or counted as a new successful kernel.
    for name, expected in p["retained_files"].items():
        reader.require(sha(reader.content(name)) == expected, "retained FFN evidence/history bytes differ: " + name)
    aliases = config.get("current_runtime_sources", {})
    for name, expected in reader.protocol["source_bindings"].items():
        source = "lark_kernels/" + name[7:] if name.startswith("python/") else name
        path = aliases.get(source, source)
        reader.require(path in declared and sha(reader.content(path)) == expected,
                       "matched FFN SDK runtime source identity differs: " + source)
    result = Packet(root / p["prefix"]).packet()
    result.update(independent_source_bound_development_pipelines=1, recorded_source_CI_positive_builds=ci_builds,
                  recorded_source_CI_commit=p["published_source"], recorded_source_CI_run=p["ci_run"],
                  successful_source_CI_jobs=24, anonymous_publication_files=public_files,
                  original_kernel_input_files_byte_bound=5, fresh_experiments_by_ledger=False,
                  scope="One full-size compiled FFN development pipeline with two actual stateful PTX launches "
                        "and their shared 65536-value FP16 intermediate. All 256/1024 reduction terms, "
                        "65536/16384 lanes and 16384 reference outputs retain their original contracts. "
                        "Three local checks and two CI checks concern this same pipeline. Its four direct "
                        "Lean controls and 31 false recordings are custom controls. All earlier development "
                        "failures and cancelled CI remain retained. Abstract scalar, logical pointer, parser "
                        "and sequential host-launch correspondence remain trusted. No IEEE/error bound, "
                        "NVIDIA execution, original optimized program/model result or paper completion is added.")
    return result
