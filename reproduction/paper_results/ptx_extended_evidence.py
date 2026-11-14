"""Inspect retained BMM/Linear recordings without executing captured code.

The authored protocol data fixes the recorded identities, limits and scope.
Every archive member is read and hashed, including failed development history
and compiled objects. This is evidence validation, not a new Lean/model/GPU run
or an IEEE, NVIDIA or original-paper reproduction claim. Older readers and
their archive bounds are unchanged.
"""

import gzip
import hashlib
import io
import json
import math
from pathlib import Path, PurePosixPath
import re
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CERTIFICATE_TAGS = ("source_program", "reference_body", "launch", "race_free",
                    "segment_equivalence", "kernel_eq_spec")
PROTOCOLS = json.loads(Path(__file__).with_name("ptx_extended_protocols.json").read_text())
CONFIG_KEYS = {"bmm": "ptx_batched_proof", "linear": "ptx_linear_proof"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def same_json(actual, expected):
    options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
    return json.dumps(actual, **options) == json.dumps(expected, **options)


class Recording:
    def __init__(self, root, kind, declared=None):
        self.root = Path(root).resolve()
        self.kind = kind
        self.protocol = PROTOCOLS[kind]
        self.declared = declared

    def require(self, ok, message):
        if not ok:
            raise ValueError("PTX " + self.kind + " " + message)

    def path(self, name):
        self.require(type(name) is str, "string evidence path required")
        path = PurePosixPath(name)
        self.require(bool(path.parts) and not path.is_absolute() and ".." not in path.parts
                     and str(path) == name, "unsafe recording path")
        return path

    def content(self, name):
        self.path(name)
        path = self.root / name
        self.require(path.is_file() and not path.is_symlink()
                     and path.resolve().is_relative_to(self.root), "recording path differs")
        self.require(self.declared is None or name in self.declared, "undeclared recording file")
        return path.read_bytes()

    def read(self, name):
        return json.loads(self.content(name))

    def fields(self, record, expected, gate):
        self.require(type(record) is dict and all(k in record and same_json(record[k], v)
                     for k, v in expected.items()), gate)

    def counters(self, record, expected, gate):
        self.require(all(type(record.get(k)) is int and record[k] == v
                         for k, v in expected.items()), gate)

    def audits(self, data, expected):
        matches = re.findall(
            r"'([^']+)'\s+(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
            data.decode())
        result = {name: sorted(v.strip() for v in values.split(",") if v.strip())
                  for name, _, values in matches}
        self.require(len(result) == len(matches) and set(result) == set(expected)
                     and all(set(value) <= ALLOWED for value in result.values()),
                     "positive axiom audit differs")
        return result

    def inventory(self, entries):
        self.require("manifest.json" in entries, "inner recording manifest missing")
        self.require({n: sha(data) for n, data in entries.items() if n != "manifest.json"}
                     == json.loads(entries["manifest.json"]), "inner recording inventory differs")

    def archive(self, label, binding):
        inventory_data = self.content(label + "-files.json")
        inventory = json.loads(inventory_data)
        data = self.content(label + ".tar.gz")
        cap = self.protocol["archive_uncompressed_caps"][label]
        self.counters(binding, {"files": self.protocol["archive_member_counts"][label],
                                "archive_bytes": len(data)}, "archive size/inventory differs")
        self.require(type(binding.get("uncompressed_bytes")) is int
                     and 0 <= binding["uncompressed_bytes"] <= cap and len(data) <= 90_000_000
                     and sha(data) == binding["archive_sha256"]
                     and sha(inventory_data) == binding["inventory_sha256"], "archive binding differs")
        entries, size = {}, 0
        with gzip.GzipFile(fileobj=io.BytesIO(data)) as decoded, \
                tarfile.open(fileobj=decoded, mode="r|") as archive:
            for member in archive:
                self.path(member.name)
                self.require(member.isfile() and member.name not in entries
                             and member.name in inventory and 0 <= member.size <= 10_000_000,
                             "unsafe archive member")
                size += member.size
                self.require(size <= cap and len(entries) < binding["files"],
                             "archive size/inventory differs")
                value = archive.extractfile(member).read()
                self.require(len(value) == member.size and sha(value) == inventory[member.name],
                             "archive member hash differs")
                entries[member.name] = value
        self.require(set(entries) == set(inventory) and len(entries) == binding["files"]
                     and size == binding["uncompressed_bytes"], "archive size/inventory differs")
        pinned = self.protocol["immutable_inventory_sha256"].get(label)
        self.require(pinned is None or sha(inventory_data) == pinned,
                     "retained development/test inventory differs")
        return entries

    def check(self, row, log, command, *, accepted=True):
        seconds, timeout = row.get("seconds"), row.get("timeout_seconds")
        self.require(type(row.get("exit_code")) is int
                     and (row["exit_code"] == 0 if accepted else row["exit_code"] != 0)
                     and row.get("timed_out") is False and row.get("log_sha256") == sha(log)
                     and type(row.get("command")) is list and row["command"][1:] == command
                     and type(seconds) in (int, float) and math.isfinite(seconds) and 0 <= seconds <= 180
                     and type(timeout) is int and timeout == 180,
                     "recorded checker completion/budget/log differs")

    def positive(self, entries, *, older=None, accepted=True):
        self.inventory(entries)
        p, c = self.protocol, self.protocol["contract"]
        proof = json.loads(entries["results.json"])
        identity = {"status": "verified-source-bound-full-PTX-" + self.kind.upper(),
                    "main_sha256": c["main_sha256"], "source_bindings_sha256": c["source_bindings_sha256"],
                    "source_bound_proof_accepted": True, "source_bound_development_proofs": 1}
        if older:
            identity.update(older)
        self.fields(proof, identity, "positive source/contract/proof binding differs")
        keys = ("shapes", "launch", "unchanged_CUDA_contract_fuel", "limits", "input_bindings",
                "lean_binary_sha256", "scope", "nvidia_execution", "original_paper_fully_reproduced")
        self.fields(proof, {k: c[k] for k in keys}, "positive execution/contract scope differs")
        self.fields(proof, {"profile": p["identity"]["profile"], "source_language": "ptx",
                    "reference_contract_language": "cuda", "old_owned_olean_cache_used": False,
                    "dtypes": ["float16"] * len(c["shapes"])}, "positive source/contract/proof binding differs")
        self.counters(proof, {"PTX_instructions": p["counters"]["PTX_instructions"],
                      "source_bound_development_proofs": int(accepted),
                      "owned_Lean_modules_freshly_compiled": len(p["modules"]),
                      "model_calls": 0, "gpu_trials": 0, "new_registered_source_certificates": 0},
                      "positive proof counters differ")
        self.require(all(sha(entries[n]) == digest for n, digest in c["input_bindings"].items())
                     and sha(entries["Main.lean"]) == proof["main_sha256"],
                     "positive source/contract/proof binding differs")
        self.require(same_json(json.loads(entries["reference-ast.json"]), p["reference_ast"])
                     and proof["reference_ast_sha256"] == sha(entries["reference-ast.json"]),
                     "positive reference AST differs")
        bindings = json.loads(entries["source-bindings.json"])
        self.require(sha(entries["source-bindings.json"]) == proof["source_bindings_sha256"]
                     and len(bindings) == p["counters"]["owned_source_files"]
                     and all(sha(entries["owned-sources/" + n]) == digest for n, digest in bindings.items()),
                     "trusted source identity differs")
        expected = {*c["input_bindings"], "Main.lean", "Main.log", "translation.json", "reference-ast.json",
                    "source-bindings.json", "results.json", "manifest.json"}
        expected.update("owned-sources/" + name for name in bindings)
        for module in p["modules"]:
            expected.update((module + ".log", "modules/Lark/" + module + ".lean",
                             "modules/Lark/" + module + ".olean"))
        if "replay.json" in entries:
            expected.update(("replay.json", "proof-export-manifest.json"))
        self.require(set(entries) == expected, "positive recording roster differs")
        self.require([row["module"] for row in proof["module_checks"]]
                     == ["Lark." + module for module in p["modules"]], "positive module roster differs")
        library = {}
        for (module, namespace), row in zip(p["modules"].items(), proof["module_checks"], strict=True):
            source = entries["owned-sources/lean/Lark/" + module + ".lean"]
            self.require(entries["modules/Lark/" + module + ".lean"] == source,
                         "compiled module source differs")
            self.check(row, entries[module + ".log"], ["-o", "Lark/" + module + ".olean",
                                                       "Lark/" + module + ".lean"])
            tags = re.findall(r"^#print axioms (\S+)", source.decode(), re.M)
            tags = [t if t.startswith(namespace + ".") else namespace + "." + t for t in tags]
            part = self.audits(entries[module + ".log"], tags)
            self.require(not set(library).intersection(part), "duplicate library audit")
            library.update(part)
        self.require(proof["library_axiom_audits"] == library
                     and len(library) == p["counters"]["library_axiom_audits_per_check"],
                     "positive axiom audit differs")
        self.check(proof["main_check"], entries["Main.log"], ["Main.lean"], accepted=accepted)
        if accepted:
            tags = [p["certificate_namespace"] + "." + name for name in CERTIFICATE_TAGS]
            self.require(proof["axiom_audits"] == self.audits(entries["Main.log"], tags),
                         "positive axiom audit differs")
        else:
            self.require(b"maximum recursion depth" in entries["Main.log"]
                         and proof["source_bound_proof_accepted"] is False,
                         "failed official export relabeled as accepted")
        elapsed = proof["import_build_seconds"]
        self.require(type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 600,
                     "source import aggregate budget differs")
        return proof

    def replay(self, entries, proof, export_manifest):
        replay = json.loads(entries["replay.json"])
        self.fields(replay, {"status": "fresh-source-only-PTX-" + self.kind.upper() + "-proof-replay-passed",
                    "main_regenerated_identically": True, "recording_manifest_sha256": export_manifest,
                    "fresh_export_manifest_sha256": sha(entries["proof-export-manifest.json"]),
                    "main_sha256": self.protocol["contract"]["main_sha256"],
                    "old_owned_olean_cache_used": False, "nvidia_execution": False,
                    "original_paper_fully_reproduced": False, "fresh_export_axiom_audits": proof["axiom_audits"]},
                    "fresh source-only replay binding differs")
        self.counters(replay, {"owned_modules_freshly_compiled": len(self.protocol["modules"]),
                      "positive_rechecks": 1, "source_bound_proofs_added": 0, "model_calls": 0,
                      "gpu_trials": 0, "new_registered_source_certificates": 0}, "replay counters differ")
        self.require(json.loads(entries["proof-export-manifest.json"])
                     == {n: sha(value) for n, value in entries.items()
                         if n not in ("manifest.json", "replay.json", "proof-export-manifest.json")},
                     "fresh export inventory differs")

    def controls(self, entries, positive, export_manifest):
        self.inventory(entries)
        controls = json.loads(entries["results.json"])
        self.fields(controls, {"status": "full-size-PTX-" + self.kind.upper() + "-source-controls-passed",
                    "recording_manifest_sha256": export_manifest, "old_owned_olean_cache_used": False,
                    "nvidia_execution": False, "original_paper_fully_reproduced": False,
                    "positive": json.loads(positive["replay.json"])}, "source-control scope differs")
        self.require(controls == self.read("controls-results.json")
                     and len(controls["negative_controls"]) == 4
                     and [c["control"] for c in controls["negative_controls"]]
                     == self.protocol["negative_controls"], "source-control roster differs")
        self.counters(controls, {"positive_controls": 1, "direct_Lean_negative_controls": 4,
                      "timeouts": 0, "owned_modules_freshly_compiled": len(self.protocol["modules"]),
                      "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
                      "model_calls": 0, "gpu_trials": 0}, "control execution counters differ")
        for control in controls["negative_controls"]:
            base = control["control"] + "/"
            log, main = entries[base + "Main.log"], entries[base + "Main.lean"]
            self.fields(control, {"reader_accepted": True,
                        "channel": "source-program-equality-proof-refused", "general_kernel_falsity_claim": False,
                        "all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged": True,
                        "source_sha256": sha(entries[base + "kernel.ptx"]), "main_sha256": sha(main)},
                        "direct Lean binding-control scope differs")
            self.counters(control, {"PTX_instructions": self.protocol["counters"]["PTX_instructions"],
                          "source_fragments_changed": 1}, "direct Lean binding-control scope differs")
            self.require(json.loads(entries[base + "results.json"]) == control
                         and all(sha(entries[base + n]) == digest
                                 for n, digest in self.protocol["contract"]["input_bindings"].items()
                                 if n != "kernel.ptx"), "direct Lean binding-control scope differs")
            self.check(control["Lean"], log, ["Main.lean"], accepted=False)
            lines = [i + 1 for i, line in enumerate(main.decode().splitlines())
                     if line.startswith("theorem source_program ")]
            errors = {int(n) for n in re.findall(rb"Main\.lean:([0-9]+):[0-9]+: error:", log)}
            self.require(len(lines) == 1 and lines[0] in errors
                         and b"tactic 'decide' proved that" in log and b"is false" in log
                         and not any(marker in log for marker in (
                             b"maximum recursion", b"maximum number of heartbeats", b"Stack overflow")),
                         "direct Lean binding-control refusal differs")

    def installed_wheel(self, installed_entries, wheel_entries, export):
        self.inventory(installed_entries)
        self.inventory(wheel_entries)
        p = self.protocol
        installed, build = (json.loads(installed_entries["results.json"]),
                            json.loads(wheel_entries["build-results.json"]))
        self.require(installed == self.read("installed-wheel-results.json")
                     and build == self.read("wheel-build-results.json"), "copied wheel summary differs")
        expected = {"status": "installed-wheel-source-only-PTX-" + self.kind.upper() + "-replay-passed",
                    "checkout_imported": False, "isolated_mode": True, "git_on_PATH": False,
                    "network_during_install_and_replay": False, "nvidia_execution": False,
                    "original_paper_fully_reproduced": False}
        expected.update(dict.fromkeys(p["installed_true_flags"], True))
        self.fields(installed, expected, "installed-wheel replay differs")
        self.counters(installed, {"exit_code": 0, "owned_modules_freshly_compiled": len(p["modules"]),
                      "source_bound_proofs_added": 0, "model_calls": 0, "gpu_trials": 0,
                      "new_registered_source_certificates": 0}, "installed-wheel execution counters differ")
        self.fields(build, {"status": "wheel-built-and-all" + str(p["counters"]["owned_source_files"])
                    + "-" + self.kind.upper() + "-owned-sources-byte-checked",
                    "backend": {"setuptools": "80.9.0", "wheel": "0.45.1"},
                    p["wheel_build_included_flag"]: True, "network_during_build": False,
                    "nvidia_execution": False, "original_paper_fully_reproduced": False}, "wheel build scope differs")
        wheel = wheel_entries[build["wheel_filename"]]
        self.require(sha(wheel) == p["contract"]["wheel_sha256"] == installed["wheel_sha256"]
                     == build["wheel_sha256"], "wheel trusted identity differs")
        self.counters(build, {"exit_code": 0, "wheel_bytes": len(wheel),
                      "owned_source_bindings_checked": p["counters"]["owned_source_files"],
                      "model_calls": 0, "gpu_trials": 0, "new_registered_source_certificates": 0},
                      "wheel build counters differ")
        self.counters(installed, {"wheel_bytes": len(wheel)}, "installed-wheel byte count differs")
        with zipfile.ZipFile(io.BytesIO(wheel)) as archive:
            names = archive.namelist()
            self.require(len(names) == len(set(names)), "wheel duplicate entry")
            for name, digest in json.loads(export["source-bindings.json"]).items():
                if name.startswith("python/"):
                    path = "lark_kernels/" + name[7:]
                else:
                    matches = [n for n in names if n.endswith("/share/lark/" + name)]
                    self.require(len(matches) == 1, "wheel owned source roster differs")
                    path = matches[0]
                self.require(sha(archive.read(path)) == digest, "wheel trusted source identity differs")

    def history(self, archives):
        p = self.protocol
        data = self.content("validation-history.json")
        self.require(sha(data) == p["validation_history_sha256"], "retained development history differs")
        history = json.loads(data)
        entries = archives["development-history"]
        if self.kind == "bmm":
            for label, expected in p["older_official_exports"].items():
                accepted = label == "initial-export-v1"
                proof = self.positive(archives[label], older=expected, accepted=accepted)
                summary = "initial-export-results.json" if accepted else "failed-export-results.json"
                self.require(self.read(summary) == proof, "copied historical export summary differs")
            roots = {n.split("/")[0] for n in entries}
            self.require(roots == set(history["selected_development_history"])
                         and history["cached_development_counts_as_source_only_export"] is False
                         and history["failed_v2"]["accepted"] is False,
                         "cached/failed history counted as official proofs")
        else:
            self.require(entries["history-observations.json"] == data,
                         "copied historical observation differs")
            observations = history["earlier_actual_terminal_exit_codes"]
            observations.update({r["label"]: r["observed_terminal_exit_code"]
                                 for r in history["additional_actual_terminal_observations"]})
            self.require({n.split("/")[0] for n in entries if n != "history-observations.json"}
                         == set(observations) and len(observations) == 12
                         and sum(type(v) is int and v == 0 for v in observations.values()) == 7
                         and sum(type(v) is int and v != 0 for v in observations.values()) == 5
                         and history["failed_Lean_drafts_never_accepted"] is True
                         and history["partial_cold_v1_driver_failure_never_accepted"] is True,
                         "cached/failed history counted as official proofs")

    def packet(self):
        p = self.protocol
        manifest, report = self.read("manifest.json"), self.read("results.json")
        self.require({n.name for n in self.root.iterdir()} == set(p["packet_files"])
                     == set(manifest) | {"manifest.json"}
                     and all(sha(self.content(n)) == digest for n, digest in manifest.items()),
                     "packet inventory differs")
        self.fields(report, p["identity"], "recording identity differs")
        self.counters(report, p["counters"], "kernel/recheck/execution counters differ")
        self.fields(report, {**p["contract"], **p["report_boolean_fields"]}, "proof contract/original scope differs")
        self.require(sha(self.content("packaging-driver.py")) == p["identity"]["packaging_driver_sha256"],
                     "packaging source binding differs")
        self.require(set(report["archives"]) == set(p["archive_uncompressed_caps"]), "archive roster differs")
        archives = {label: self.archive(label, binding) for label, binding in report["archives"].items()}
        export_manifest = sha(archives["export"]["manifest.json"])
        positives = [archives["export"], archives["replay"],
                     {n.removeprefix("positive-source-only-replay/"): data
                      for n, data in archives["controls"].items() if n.startswith("positive-source-only-replay/")},
                     {n.removeprefix("source-only-replay/"): data
                      for n, data in archives["installed-wheel"].items() if n.startswith("source-only-replay/")}]
        for i, entries in enumerate(positives):
            proof = self.positive(entries)
            if i:
                self.replay(entries, proof, export_manifest)
        self.require(self.read("proof-results.json") == json.loads(positives[0]["results.json"])
                     and self.read("replay-results.json") == json.loads(positives[1]["replay.json"]),
                     "copied proof/replay summary differs")
        self.controls(archives["controls"], positives[2], export_manifest)
        self.installed_wheel(archives["installed-wheel"], archives["wheel-build"], positives[0])
        self.inventory(archives["sdk-tests"])
        sdk = json.loads(archives["sdk-tests"]["results.json"])
        self.require(sdk == self.read("sdk-test-results.json")
                     and sha(self.content("sdk-test-source.py")) == sdk["test_source_sha256"]
                     == p["sdk_test_source_sha256"], "SDK test source/summary differs")
        self.fields(sdk, {"status": self.kind.upper() + "-SDK-complete-proof-replay-adversarial-test-passed",
                    "timed_out": False, "original_paper_fully_reproduced": False}, "SDK test scope differs")
        self.counters(sdk, {"exit_code": 0, "model_calls": 0, "gpu_trials": 0}, "SDK test counters differ")
        self.history(archives)
        return {**p["counters"], "shapes": p["contract"]["shapes"], "source_commit": p["published_source"],
                "archive_members_checked": sum(len(v) for v in archives.values()),
                "archives_checked": len(archives), "fresh_experiments_by_ledger": False,
                "nvidia_execution": False, "original_paper_fully_reproduced": False,
                "scope": "Recorded exact-source complete abstract PTX " + self.kind.upper()
                         + " proof and replay/control/history bindings for one independent kernel. "
                         "Repeated checks and failed or partial development attempts add no independent "
                         "kernel, model success, IEEE/error-bound, NVIDIA conformance or original paper result."}


def check_recording_packet(root, *, kind, declared=None):
    return Recording(root, kind, declared).packet()


def check_source_ci(reader, summary, run, response):
    p = reader.protocol
    jobs, names = response["jobs"], set(p["ci_jobs"])
    count = len(names)
    reader.fields(run, {"id": p["ci_run"], "head_sha": p["published_source"],
                  "event": "push", "name": "Verify", "head_branch": p["ci_branch"],
                  "status": "completed", "conclusion": "success", "run_attempt": 1},
                  "actual source CI differs")
    reader.require(type(response.get("total_count")) is int
                   and response["total_count"] == len(jobs) == len({j["id"] for j in jobs}) == count
                   and {j["name"] for j in jobs} == names
                   and all(j["status"] == "completed" and j["conclusion"] == "success"
                           and type(j["run_id"]) is int and j["run_id"] == p["ci_run"] for j in jobs),
                   "actual source CI differs")
    reader.fields(summary, {"status": "exact-source-CI-all-" + str(count) + "-passed",
                  "source_commit": p["published_source"], "run_id": p["ci_run"],
                  "original_paper_fully_reproduced": False}, "actual source CI differs")
    reader.require(len(summary["expected_jobs"]) == count
                   and set(summary["expected_jobs"]) == names, "actual source CI differs")
    reader.counters(summary, {"successful_jobs": count, "model_calls": 0, "gpu_trials": 0,
                    "CI_reruns": 0, "new_registered_source_certificates": 0},
                    "source CI execution counters differ")


def check_ptx_extended_evidence(config, *, kind, root=ROOT):
    root, p = Path(root).resolve(), PROTOCOLS[kind]
    spec = {k: p[k] for k in ("prefix", "publication_prefix", "ci_prefix", "main_prefix")}
    reader = Recording(root, kind, {n for group in config["evidence_groups"].values() for n in group})
    reader.require(config[CONFIG_KEYS[kind]] == spec, "declared evidence roster differs")
    declared_packet = {n[len(p["prefix"]) + 1:] for n in reader.declared if n.startswith(p["prefix"] + "/")}
    report = check_recording_packet(root / p["prefix"], kind=kind, declared=declared_packet)

    def content(prefix, name):
        return reader.content(prefix + "/" + name)

    def read(prefix, name):
        return json.loads(content(prefix, name))

    for key, names in (
        ("publication_prefix", {"manifest.json", "results.json", "binding.json", "verifier.py"}),
        ("ci_prefix", {"manifest.json", "results.json", "run.json", "jobs.json", "observer.py", "progress.json"}),
        ("main_prefix", {"manifest.json", "results.json", "progress.json", "update.json", "promotion-driver.py"}),
    ):
        prefix = p[key]
        manifest = read(prefix, "manifest.json")
        reader.require({n[len(prefix) + 1:] for n in reader.declared if n.startswith(prefix + "/")}
                       == names == set(manifest) | {"manifest.json"}
                       and {n.name for n in (root / prefix).iterdir()} == names
                       and all(sha(content(prefix, n)) == digest for n, digest in manifest.items()),
                       "auxiliary inventory differs")
    pub = read(p["publication_prefix"], "results.json")
    reader.fields(pub, {"status": "anonymous-exact-source-full-size-PTX-" + kind.upper()
                  + "-proof-publication-verified", "source_commit": p["published_source"],
                  "all_downloads_match_committed_bytes": True, "tls_verification": True,
                  "authorization_header": False, "original_paper_fully_reproduced": False},
                  "anonymous publication scope differs")
    reader.counters(pub, p["publication_counters"], "publication execution counters differ")
    rows = pub["downloaded_files"]
    reader.require(len(rows) == len(p["publication_files"])
                   and {r["path"] for r in rows} == set(p["publication_files"])
                   and sum(r["bytes"] for r in rows) == p["publication_bytes"],
                   "anonymous publication roster differs")
    for row in rows:
        reader.fields(row, {**p["publication_files"][row["path"]], "http_status": 200,
                      "curl_ssl_verify_result": 0, "tls_verification": True,
                      "authorization_header": False, "matches_committed_bytes": True},
                      "anonymous publication scope differs")
        attempts = row["download_attempts"]
        reader.require(bool(attempts) and any(type(r.get("curl_exit_code")) is int
                       and r["curl_exit_code"] == 0 and r["http_status"] == 200
                       and r["curl_ssl_verify_result"] == 0 for r in attempts),
                       "anonymous download observation differs")
        if row["path"].startswith(p["prefix"] + "/"):
            reader.require(sha(reader.content(row["path"])) == row["sha256"],
                           "published packet bytes differ")
    binding = read(p["publication_prefix"], "binding.json")
    reader.fields(binding, {"source_commit": p["published_source"], "observed_exit_code": 0,
                  "verifier_sha256": sha(content(p["publication_prefix"], "verifier.py")),
                  "anonymous_results_sha256": sha(content(p["publication_prefix"], "results.json")),
                  "proof_packet_manifest_sha256": sha(reader.content(p["prefix"] + "/manifest.json")),
                  "original_paper_fully_reproduced": False}, "publication verifier/result/source binding differs")
    reader.counters(binding, {"observed_exit_code": 0, "model_calls": 0, "fresh_lean_checks": 0,
                              "gpu_trials": 0}, "publication binding execution counters differ")
    ci = p["ci_prefix"]
    summary, run, jobs = (read(ci, name) for name in ("results.json", "run.json", "jobs.json"))
    check_source_ci(reader, summary, run, jobs)
    reader.require(summary["observer_sha256"] == sha(content(ci, "observer.py")),
                   "source CI observer binding differs")
    main = p["main_prefix"]
    promotion = read(main, "results.json")
    reader.fields(promotion, {"status": ("BMM" if kind == "bmm" else "Linear") + "-main-fast-forward-complete",
                  "source_checkpoint": p["published_source"], "old_main": p["old_main"],
                  "promoted_commit": p["promoted_main"], "source_CI_executed_for_promoted_commit": False,
                  "original_paper_fully_reproduced": False,
                  "helper_sha256": sha(content(main, "promotion-driver.py"))},
                  "actual completed main-promotion receipt differs")
    reader.counters(promotion, {"model_calls_by_promotion": 0, "fresh_lean_checks_by_promotion": 0,
                                "gpu_trials_by_promotion": 0}, "main promotion execution counters differ")
    check_source_ci(reader, summary, promotion["source_ci"], promotion["source_ci_jobs"])
    reader.require(set(promotion["checks"]) == set(p["main_checks"])
                   and all(v is True for v in promotion["checks"].values())
                   and same_json(promotion["changed_paths_after_checked_source"], p["post_source_paths"])
                   and same_json(read(main, "update.json"), {"sha": p["promoted_main"], "force": False})
                   and promotion["remote_update"]["ref"] == "refs/heads/main"
                   and promotion["remote_update"]["object"]["type"] == "commit"
                   and promotion["remote_update"]["object"]["sha"] == p["promoted_main"],
                   "main promotion guard/update differs")
    if kind == "linear":
        bmm = PROTOCOLS["bmm"]
        reader.require(binding["preceding_BMM_main_receipt_manifest_sha256"]
                       == sha(reader.content(bmm["main_prefix"] + "/manifest.json"))
                       and p["old_main"] == bmm["promoted_main"], "preceding BMM main receipt differs")
    report.update(anonymous_publication_files=len(rows), successful_source_CI_jobs=len(p["ci_jobs"]),
                  main_promoted_commit=p["promoted_main"], metadata_only_promotion_reuses_source_CI=True)
    return report


def check_ptx_batched_evidence(config, root=ROOT):
    return check_ptx_extended_evidence(config, kind="bmm", root=root)


def check_ptx_linear_evidence(config, root=ROOT):
    return check_ptx_extended_evidence(config, kind="linear", root=root)
