"""Read the complete recorded RoPE proof/history as data, without Git or execution.

Only standard-library modules are used. Captured Python, Lean, wheels, binaries
and object files are never imported, extracted, executed or loaded. This checks
recorded evidence, not a fresh proof or paper/model/GPU result.
"""

import argparse
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
CERTIFICATE_TAGS = ("source_program", "reference_body", "reference_denotation", "launch", "race_free",
                    "segment_equivalence", "kernel_eq_spec")
PROTOCOLS = json.loads(Path(__file__).with_name("ptx_rotary_protocol.json").read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def same_json(actual, expected):
    options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
    return json.dumps(actual, **options) == json.dumps(expected, **options)


class Recording:
    def __init__(self, root, kind, declared=None):
        self.root = Path(root).resolve()
        self.kind = kind
        self.protocol = PROTOCOLS
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
        self.require(path.stat().st_size <= 90_000_000, "recording file size bound exceeded")
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
        self.require(not any(x in data for x in (b"sorryAx", b"error:", b"Stack overflow",
                         b"maximum recursion", b"maximum number of heartbeats")),
                     "positive Lean log contains an error or unproved axiom")
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
        self.require(sha(entries["translation.json"]) == p["translation_sha256"]
                     and bindings == p["owned_source_bindings"], "actual translation/trusted SDK identity differs")
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

    def direct_controls(self, entries):
        self.inventory(entries)
        report = json.loads(entries["results.json"])
        self.require(report == self.read("direct-controls-results.json"), "copied direct controls differ")
        self.fields(report, {"status": "all-four-direct-Lean-RoPE-controls-rejected",
                    "source_commit": self.protocol["identity"]["SDK_source_commit"],
                    "original_paper_fully_reproduced": False}, "direct-control scope differs")
        self.counters(report, {"negative_controls": 4, "negative_timeouts": 0,
                      "resource_limit_failures": 0, "model_calls": 0, "GPU_trials": 0,
                      "new_kernel_proofs": 0}, "direct-control counters differ")
        self.require([r["name"] for r in report["controls"]] == self.protocol["direct_controls"],
                     "direct-control roster differs")
        for row in report["controls"]:
            prefix = row["name"] + "/"
            part = {n[len(prefix):]: v for n, v in entries.items() if n.startswith(prefix)}
            self.inventory(part)
            main, log = part["Main.lean"], part["Main.log"]
            gate = "reference_body" if row["name"] == self.protocol["direct_controls"][-1] else "source_program"
            self.fields(row, {"expected_gate": gate, "rejected_at_expected_gate": True,
                        "resource_failure": False, "expected_rejection_verified": True,
                        "main_sha256": sha(main), "original_paper_fully_reproduced": False},
                        "direct-control refusal scope differs")
            self.counters(row, {"new_kernel_proofs": 0}, "direct-control proof count differs")
            self.require(json.loads(part["results.json"]) == row
                         and row["input_bindings"] == {n: sha(part[n]) for n in self.protocol["contract"]["input_bindings"]}
                         and all(sha(part[n]) == digest for n, digest in self.protocol["contract"]["input_bindings"].items()
                                 if n != "kernel.ptx"), "direct-control input binding differs")
            self.check(row["check"], log, ["Main.lean"], accepted=False)
            lines = [i + 1 for i, line in enumerate(main.decode().splitlines())
                     if line.startswith("theorem " + gate + " ")]
            errors = {int(n) for n in re.findall(rb"Main\.lean:([0-9]+):[0-9]+: error:", log)}
            expected_error = ((b"tactic 'rfl' failed" in log and b"not definitionally equal" in log)
                              if gate == "reference_body" else
                              (b"tactic 'decide' proved that" in log and b"is false" in log))
            self.require(len(lines) == 1 and type(row["expected_Main_line"]) is int
                         and lines[0] == row["expected_Main_line"] and lines[0] in errors
                         and expected_error
                         and not any(marker.lower() in log.lower() for marker in (
                             b"maximum recursion", b"maximum number of heartbeats", b"Stack overflow", b"deep recursion")),
                         "direct Lean binding-control refusal differs")
            if gate == "reference_body":
                self.fields(json.loads(part["bypass.json"]),
                            {"input_source_and_reference_unchanged": True}, "reference bypass scope differs")

    def rehashed_controls(self, entries):
        self.inventory(entries)
        report = json.loads(entries["results.json"])
        self.require(report == self.read("rehashed-controls-results.json"), "copied rehashed controls differ")
        self.fields(report, {"status": "all17-coherently-rehashed-RoPE-controls-rejected",
                    "all_false_payloads_retained": True, "original_paper_fully_reproduced": False},
                    "rehashed-control scope differs")
        self.counters(report, {"negative_controls": 17, "fresh_Lean_checks": 0,
                      "GPU_trials": 0, "model_calls": 0}, "rehashed-control counters differ")
        self.require([r["name"] for r in report["checks"]] == self.protocol["rehashed_controls"],
                     "rehashed-control roster differs")
        for row in report["checks"]:
            prefix = row["name"] + "/"
            part = {n[len(prefix):]: v for n, v in entries.items() if n.startswith(prefix)}
            self.inventory(part)
            recording = {n.removeprefix("recording/"): v for n, v in part.items() if n.startswith("recording/")}
            self.inventory(recording)
            self.require(json.loads(part["results.json"]) == row
                         and row["complete_false_recording_manifest_sha256"] == sha(recording["manifest.json"]),
                         "complete false recording binding differs")
            self.fields(row, {"status": "rejected-before-fresh-Lean-work", "output_created": False},
                        "rehashed control performed or claimed a fresh check")
            self.require(type(row["detail"]) is str and bool(row["detail"])
                         and "inventory" not in row["detail"].lower(), "refusal was not semantic")
            try:
                self.positive(recording)
            except ValueError:
                pass
            else:
                self.require(False, "coherently rehashed false recording accepted")

    def wheel(self, installed_entries, wheel_entries, export):
        self.inventory(installed_entries)
        self.inventory(wheel_entries)
        installed = json.loads(installed_entries["results.json"])
        build = json.loads(wheel_entries["build-results.json"])
        self.require(installed == self.read("installed-wheel-results.json")
                     and build == self.read("wheel-build-results.json"), "copied wheel summary differs")
        self.fields(installed, {"status": "installed-wheel-outside-Git-full-RoPE-replay-passed",
                    "wheel_sha256": self.protocol["contract"]["wheel_sha256"],
                    "wheel_source_commit": self.protocol["identity"]["wheel_source_commit"],
                    "network_during_install": False, "original_paper_fully_reproduced": False},
                    "installed-wheel replay scope differs")
        self.counters(installed, {"matched_owned_sources": 64, "fresh_owned_Lean_modules": 8,
                      "positive_rechecks": 1, "source_bound_proofs_added": 0,
                      "model_calls": 0, "GPU_trials": 0}, "installed-wheel replay counters differ")
        self.fields(build, {"status": "wheel-built-and-all64-ROTARY-owned-sources-byte-checked",
                    "backend": {"setuptools": "80.9.0", "wheel": "0.45.1"},
                    "source_commit": self.protocol["identity"]["wheel_source_commit"],
                    "all_eight_owned_Lean_files_included": True, "network_during_build": False,
                    "nvidia_execution": False, "original_paper_fully_reproduced": False},
                    "wheel build scope differs")
        wheel = wheel_entries[build["wheel_filename"]]
        self.require(sha(wheel) == installed["wheel_sha256"] == build["wheel_sha256"], "wheel identity differs")
        self.counters(build, {"exit_code": 0, "wheel_bytes": len(wheel), "owned_source_bindings_checked": 64,
                      "model_calls": 0, "gpu_trials": 0, "new_registered_source_certificates": 0},
                      "wheel build counters differ")
        identity = json.loads(installed_entries["installed-identity.json"])
        self.require(identity["source_bindings"] == self.protocol["owned_source_bindings"],
                     "installed identity differs")
        links = self.read("runtime-links.json")
        self.require(links == self.protocol["runtime_links"], "installed original link metadata differs")
        with zipfile.ZipFile(io.BytesIO(wheel)) as archive:
            names = archive.namelist()
            self.require(len(names) == len(set(names)), "wheel duplicate entry")
            for name, digest in json.loads(export["source-bindings.json"]).items():
                if name.startswith("python/"):
                    path = "lark_kernels/" + name[7:]
                    installed_path = "venv/lib/python3.12/site-packages/" + path
                else:
                    matches = [n for n in names if n.endswith("/share/lark/" + name)]
                    self.require(len(matches) == 1, "wheel owned source roster differs")
                    path = matches[0]
                    installed_path = "venv/share/lark/" + name
                self.require(sha(archive.read(path)) == digest
                             == sha(installed_entries[installed_path]), "wheel/installed trusted source differs")

    def history(self, entries, preparation):
        raw = self.content("validation-history.json")
        self.require(sha(raw) == self.protocol["validation_history_sha256"], "retained history differs")
        history = json.loads(raw)
        self.fields(history, {"all_payloads_preserved": True,
                    "cached_development_counts_as_source_only_export": False,
                    "failed_Lean_drafts_never_accepted": True}, "development scope differs")
        self.counters(history, {"passed": 6, "failed": 11, "failed_official_exports": 0},
                      "development counts differ")
        self.require(len(history["attempts"]) == 17
                     and {n.split("/")[0] for n in entries}
                     == {Path(row["path"]).name for row in history["attempts"]}, "development roster differs")
        accepted = 0
        for row in history["attempts"]:
            prefix = Path(row["path"]).name + "/"
            part = {n[len(prefix):]: v for n, v in entries.items() if n.startswith(prefix)}
            self.inventory(part)
            result = json.loads(part["results.json"])
            passed = row["check"]["exit_code"] == 0
            accepted += int(passed)
            self.require(result["check"] == row["check"]
                         and result["status"] == row["status"]
                         == "bounded-development-module-typecheck-" + ("passed" if passed else "failed")
                         and sha(part["modules/Lark/" + row["module"] + ".lean"])
                         == result["module_source_sha256"] == row["source_sha256"],
                         "development source/completion identity differs")
            self.fields(result, {"fresh_source_only_SDK_validation": False,
                        "original_paper_fully_reproduced": False,
                        "limits": self.protocol["contract"]["limits"]}, "cached development scope differs")
            self.counters(result, {"new_kernel_proofs": 0, "GPU_trials": 0, "model_calls": 0},
                          "partial/failed development counted as a kernel")
            self.check(result["check"], part["check.log"], ["-o", "Lark/" + row["module"] + ".olean",
                       "Lark/" + row["module"] + ".lean"], accepted=passed)
            if passed:
                self.require(result["axiom_audits"] == self.audits(part["check.log"], result["axiom_audits"]),
                             "accepted development axiom audit differs")
        self.require(accepted == 6, "development accepted count differs")
        self.require({n.split("/")[0] for n in preparation} == set(self.protocol["preparation_roots"]),
                     "preparation/failure history roster differs")
        for name in self.protocol["preparation_roots"]:
            prefix = name + "/"
            self.inventory({n[len(prefix):]: v for n, v in preparation.items() if n.startswith(prefix)})
        prefix = Path(history["failed_wheel_preflight_retained"]).name + "/"
        failure = json.loads(preparation[prefix + "failed-preflight.json"])
        self.require(failure == self.protocol["failed_wheel_preflight"], "failed wheel preflight relabeled")

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
        self.require(sha(self.content("packaging-driver.py")) == p["identity"]["packaging_driver_sha256"]
                     and set(report["archives"]) == set(p["archive_groups"])
                     and all(report["archives"][label].get("group") == category
                             for label, category in p["archive_groups"].items()), "packaging/archive roster differs")
        members = 0

        def group(name):
            nonlocal members
            entries = {}
            for label, category in p["archive_groups"].items():
                if category != name:
                    continue
                part = self.archive(label, report["archives"][label])
                self.require(not set(entries).intersection(part), "duplicate member across archive parts")
                entries.update(part)
                members += len(part)
            return entries

        positives = {}
        export_manifest = None
        for label in p["positive_archives"]:
            entries = self.archive(label, report["archives"][label])
            members += len(entries)
            proof = self.positive(entries)
            self.require(proof == self.read(label + "-results.json"), "copied positive summary differs")
            if label == "export":
                export_manifest = sha(entries["manifest.json"])
            else:
                self.replay(entries, proof, export_manifest)
            positives[label] = entries
        self.direct_controls(group("direct-controls"))
        self.rehashed_controls(group("rehashed-controls"))
        self.history(group("development"), group("preparation"))
        installed = group("installed")
        self.wheel(installed, group("wheel"), positives["export"])
        self.require(json.loads(installed["results.json"])["replay_manifest_sha256"]
                     == sha(positives["wheel-replay"]["manifest.json"]), "installed replay identity differs")
        return {**p["counters"], "archive_members_checked": members, "archives_checked": len(report["archives"]),
                "SDK_source_commit": p["identity"]["SDK_source_commit"],
                "fresh_experiments_by_reader": False, "captured_code_executed": False,
                "nvidia_execution": False, "original_paper_fully_reproduced": False}


def check_recording_packet(root):
    return Recording(root, "rotary").packet()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output is not None and args.output.exists():
        parser.error("output already exists; inspect the existing observation")
    result = check_recording_packet(args.packet)
    data = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(data)
    print(data, end="")


if __name__ == "__main__":
    main()
