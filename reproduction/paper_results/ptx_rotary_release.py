"""Bind retained RoPE records to actual public source, CI and non-force promotion.

This standard-library reader validates recorded evidence. It executes no
captured SDK, Lean, compiled objects, model calls or GPU experiments.
"""

import json
from pathlib import Path
import re

if __package__:
    from .ptx_rotary_evidence import PROTOCOLS as PACKET_PROTOCOL, ROOT, Recording, same_json, sha
else:
    from ptx_rotary_evidence import PROTOCOLS as PACKET_PROTOCOL, ROOT, Recording, same_json, sha


def check_source_ci(reader, summary, run, response, protocol):
    names = set(protocol["ci_jobs"])
    jobs = response["jobs"]
    count = len(names)
    reader.require(count == len(protocol["ci_jobs"]) == 24, "actual source CI differs")
    reader.fields(run, {"id": protocol["ci_run"], "head_sha": protocol["published_source"],
                  "event": "push", "name": "Verify", "head_branch": protocol["ci_branch"],
                  "status": "completed", "conclusion": "success", "run_attempt": 1},
                  "actual source CI differs")
    reader.require(type(response.get("total_count")) is int
                   and response["total_count"] == len(jobs) == len({j["id"] for j in jobs}) == count
                   and {j["name"] for j in jobs} == names
                   and all(type(j.get("id")) is int and j["id"] > 0
                           and j["status"] == "completed" and j["conclusion"] == "success"
                           and type(j["run_id"]) is int and j["run_id"] == protocol["ci_run"] for j in jobs),
                   "actual source CI differs")
    reader.fields(summary, {"status": "exact-source-CI-all-24-passed",
                  "source_commit": protocol["published_source"], "run_id": protocol["ci_run"],
                  "original_paper_fully_reproduced": False}, "actual source CI differs")
    reader.require(len(summary["expected_jobs"]) == count
                   and set(summary["expected_jobs"]) == names, "actual source CI differs")
    reader.counters(summary, {"successful_jobs": count, "model_calls": 0, "gpu_trials": 0,
                    "CI_reruns": 0, "new_registered_source_certificates": 0},
                    "source CI execution counters differ")


def check_publication(reader, protocol, content):
    prefix = protocol["publication_prefix"]
    def read(name):
        return json.loads(content(prefix, name))

    report, binding = read("results.json"), read("binding.json")
    reader.fields(report, {"status": "anonymous-exact-source-RoPE-publication-verified",
                  "source_commit": protocol["published_source"], "base_main": protocol["old_main"],
                  "standalone_reader_outside_Git": True, "isolated_Python": True,
                  "all_TLS_verified": True, "authorization_headers_used": False,
                  "original_paper_fully_reproduced": False}, "anonymous publication scope differs")
    reader.counters(report, {"files_checked": len(protocol["publication_files"]),
                    "bytes_checked": protocol["publication_bytes"], "archives_checked": 18,
                    "archive_members_checked": 4414, "recorded_reader_exit_code": 0,
                    "fresh_Lean_checks": 0, "model_calls": 0, "gpu_trials": 0,
                    "new_registered_source_certificates": 0}, "publication execution counters differ")
    reader.fields(binding, {"source_commit": protocol["published_source"],
                  "base_main": protocol["old_main"]}, "publication verifier/result/source binding differs")
    reader.require(report["binding_sha256"] == sha(content(prefix, "binding.json"))
                   and report["verifier_sha256"] == sha(content(prefix, "verifier.py"))
                   == protocol["publication_verifier_sha256"],
                   "publication verifier/result/source binding differs")
    rows = binding["files"]
    reader.require(len(rows) == len(protocol["publication_files"])
                   and {r["path"] for r in rows} == set(protocol["publication_files"])
                   and sum(r["bytes"] for r in rows) == protocol["publication_bytes"],
                   "anonymous publication roster differs")
    for row in rows:
        reader.fields(row, {**protocol["publication_files"][row["path"]], "http_status": 200,
                      "tls_verification": True, "authorization_header": False,
                      "matches_committed_bytes": True}, "anonymous publication scope differs")
        attempts = row["download_attempts"]
        reader.require(bool(attempts) and any(type(r.get("curl_exit_code")) is int
                       and r["curl_exit_code"] == 0 and type(r.get("http_status")) is int
                       and r["http_status"] == 200 and type(r.get("ssl_verify_result")) is int
                       and r["ssl_verify_result"] == 0 for r in attempts),
                       "anonymous download observation differs")
        if row["path"].startswith(protocol["prefix"] + "/"):
            reader.require(sha(reader.content(row["path"])) == row["sha256"],
                           "published packet bytes differ")
    checked = read("reader-results.json")
    reader.fields(checked, {"fresh_experiments_by_reader": False, "captured_code_executed": False,
                  "nvidia_execution": False, "original_paper_fully_reproduced": False},
                  "anonymous recorded-reader scope differs")
    reader.counters(checked, {**PACKET_PROTOCOL["counters"], "archives_checked": 18,
                    "archive_members_checked": 4414}, "anonymous recorded-reader counters differ")
    return len(rows)


def load_protocol():
    path = Path(__file__).with_name("ptx_rotary_release_protocol.json")
    if not path.is_file():
        raise ValueError("Complete actual RoPE publication, source CI and main protocol required")
    return json.loads(path.read_text())


def check_ptx_rotary_evidence(config, root=ROOT, *, protocol=None):
    root = Path(root).resolve()
    p = load_protocol() if protocol is None else protocol
    spec = {k: p[k] for k in ("prefix", "publication_prefix", "ci_prefix", "main_prefix")}
    declared = {n for group in config["evidence_groups"].values() for n in group}
    reader = Recording(root, "rotary", declared)
    reader.require(same_json(config.get("ptx_rotary_proof"), spec), "declared evidence roster differs")
    reader.require({n[len(p["prefix"]) + 1:] for n in declared if n.startswith(p["prefix"] + "/")}
                   == set(PACKET_PROTOCOL["packet_files"]), "declared packet roster differs")

    def content(prefix, name):
        return reader.content(prefix + "/" + name)

    def read(prefix, name):
        return json.loads(content(prefix, name))

    for key in ("publication_prefix", "ci_prefix", "main_prefix"):
        prefix = p[key]
        names = set(p["auxiliary_files"][key])
        manifest = read(prefix, "manifest.json")
        reader.require({n[len(prefix) + 1:] for n in declared if n.startswith(prefix + "/")}
                       == names == set(manifest) | {"manifest.json"}
                       and {n.name for n in (root / prefix).iterdir()} == names
                       and all(sha(content(prefix, n)) == digest for n, digest in manifest.items()),
                       "auxiliary inventory differs")
    packet = Recording(root / p["prefix"], "rotary").packet()
    public_files = check_publication(reader, p, content)
    ci = p["ci_prefix"]
    summary, run, jobs = (read(ci, name) for name in ("results.json", "run.json", "jobs.json"))
    check_source_ci(reader, summary, run, jobs, p)
    reader.require(summary["observer_sha256"] == sha(content(ci, "observer.py"))
                   == p["ci_observer_sha256"],
                   "source CI observer binding differs")
    main = p["main_prefix"]
    promotion = read(main, "results.json")
    reader.fields(promotion, {"status": p["main_status"], "source_checkpoint": p["published_source"],
                  "old_main": p["old_main"], "promoted_commit": p["promoted_main"],
                  "source_CI_executed_for_promoted_commit": False, "force": False,
                  "original_paper_fully_reproduced": False,
                  "helper_sha256": sha(content(main, "promotion-driver.py"))},
                  "actual completed main-promotion receipt differs")
    reader.counters(promotion, {"model_calls_by_promotion": 0, "fresh_Lean_checks_by_promotion": 0,
                                "gpu_trials_by_promotion": 0}, "main promotion execution counters differ")
    check_source_ci(reader, summary, promotion["source_ci"], promotion["source_ci_jobs"], p)
    reader.require(sha(content(main, "promotion-driver.py")) == p["promotion_driver_sha256"]
                   and re.fullmatch("[0-9a-f]{40}", p["promoted_main"]) is not None
                   and same_json(promotion["changed_paths_after_checked_source"], p["post_source_paths"])
                   and same_json(read(main, "update.json"), {"sha": p["promoted_main"], "force": False})
                   and promotion["remote_update"]["ref"] == "refs/heads/main"
                   and promotion["remote_update"]["object"]["type"] == "commit"
                   and promotion["remote_update"]["object"]["sha"] == p["promoted_main"],
                   "main promotion guard/update differs")
    for prefix, expected in p["retained_history_manifests"].items():
        manifest = read(prefix, "manifest.json")
        reader.require(sha(content(prefix, "manifest.json")) == expected
                       and all(sha(content(prefix, n)) == digest for n, digest in manifest.items()),
                       "retained failure/validation history differs")
    packet.update(anonymous_publication_files=public_files, successful_source_CI_jobs=24,
                  main_promoted_commit=p["promoted_main"], metadata_only_promotion_reuses_source_CI=True,
                  fresh_experiments_by_ledger=False,
                  scope="One independent unchanged full-size compiled RoPE development proof, four retained "
                        "fresh checks and three rechecks. Complete source execution, independent tensor "
                        "reference, race freedom and outside-output memory preservation use abstract scalar "
                        "operations. All development failures remain separate. No IEEE/error bound, NVIDIA "
                        "execution/conformance, original model result or original-paper completion is added.")
    return packet
