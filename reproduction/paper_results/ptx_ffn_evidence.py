"""Validate fixed recorded FFN proofs as data, independently of the SDK.

This reader uses only the standard library. Captured Python, references, Lean
and compiled objects are never executed, imported or loaded. Checking a record
does not add a proof, hardware/model experiment or original-paper result.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def same_json(actual, expected):
    options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
    return json.dumps(actual, **options) == json.dumps(expected, **options)


class Recording:
    def __init__(self, root, protocol=None):
        self.root = Path(root).resolve()
        self.protocol = protocol or json.loads(
            Path(__file__).with_name("ptx_ffn_protocol.json").read_text())

    def require(self, condition, message):
        if not condition:
            raise ValueError("PTX ffn " + message)

    def content(self, name):
        self.require(type(name) is str, "string recording path required")
        path = PurePosixPath(name)
        self.require(bool(path.parts) and not path.is_absolute() and ".." not in path.parts
                     and str(path) == name, "unsafe recording path")
        target = self.root / name
        self.require(target.is_file() and not target.is_symlink()
                     and target.resolve().is_relative_to(self.root)
                     and target.stat().st_size <= 10_000_000, "recording path/size differs")
        return target.read_bytes()

    def read(self, name):
        return json.loads(self.content(name))

    def fields(self, actual, expected, gate):
        self.require(type(actual) is dict and all(key in actual and same_json(actual[key], value)
                     for key, value in expected.items()), gate)

    def counters(self, actual, expected, gate):
        self.require(type(actual) is dict and all(type(actual.get(key)) is int and actual[key] == value
                     for key, value in expected.items()), gate)

    def inventory(self):
        paths = set()
        for path in self.root.rglob("*"):
            self.require(not path.is_symlink(), "recording symlink")
            if path.is_file():
                paths.add(path.relative_to(self.root).as_posix())
        manifest = self.read("manifest.json")
        self.require(type(manifest) is dict and paths == set(manifest) | {"manifest.json"},
                     "recording file inventory differs")
        self.require(all(sha(self.content(name)) == digest for name, digest in manifest.items()),
                     "recording bytes differ")
        return paths

    def audits(self, data, expected):
        self.require(not any(marker in data for marker in (
            b"sorryAx", b"error:", b"Stack overflow", b"maximum recursion",
            b"maximum number of heartbeats", b"maximum heartbeats", b"deep recursion")),
            "positive log contains an error or unproved axiom")
        matches = re.findall(
            r"^'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
            data.decode(), re.M)
        result = {name: sorted(part.strip() for part in values.split(",") if part.strip())
                  for name, _, values in matches}
        self.require(len(result) == len(matches) and set(result) == set(expected)
                     and all(set(value) <= ALLOWED for value in result.values()),
                     "positive axiom audit differs")
        return result

    def check(self, row, log, command):
        self.require(type(row) is dict, "checker record required")
        elapsed, timeout = row.get("seconds"), row.get("timeout_seconds")
        self.require(type(row.get("exit_code")) is int and row["exit_code"] == 0
                     and row.get("timed_out") is False and row.get("log_sha256") == sha(log)
                     and type(row.get("command")) is list and row["command"][1:] == command
                     and type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 180
                     and type(timeout) is int and timeout == 180,
                     "checker completion/resource/log binding differs")

    def positive(self):
        paths = self.inventory()
        p = self.protocol
        replay = "replay.json" in paths
        expected = set(p["base_file_roster"])
        if replay:
            expected.update(("replay.json", "proof-export-manifest.json"))
        self.require(paths == expected, "complete positive recording roster differs")
        proof = self.read("results.json")
        self.fields(proof, p["positive_fields"], "positive proof/contract/resource scope differs")
        self.require(all(sha(self.content(name)) == digest
                         for name, digest in proof["input_bindings"].items())
                     and sha(self.content("Main.lean")) == proof["main_sha256"]
                     and sha(self.content("translation.json")) == p["translation_sha256"]
                     and sha(self.content("reference-ast.json")) == proof["reference_ast_sha256"]
                     and same_json(self.read("reference-ast.json"), p["reference_AST"]),
                     "actual program/reference input binding differs")
        bindings = self.read("source-bindings.json")
        self.require(bindings == p["source_bindings"] and len(bindings) == 72
                     and sha(self.content("source-bindings.json")) == proof["source_bindings_sha256"]
                     and all(sha(self.content("owned-sources/" + name)) == digest
                             for name, digest in bindings.items()), "owned source identity differs")
        checks = proof["module_checks"]
        self.require(type(checks) is list and len(checks) == 14
                     and [row.get("module") for row in checks] == ["Lark." + name for name in p["modules"]],
                     "fresh owned-module roster differs")
        library = {}
        for name, row in zip(p["modules"], checks, strict=True):
            source = "Lark/" + name + ".lean"
            log = self.content(name + ".log")
            self.check(row, log, ["-o", source.removesuffix(".lean") + ".olean", source])
            self.require(self.content("modules/" + source) == self.content("owned-sources/lean/" + source),
                         "fresh module source differs")
            library.update(self.audits(log, p["module_audit_names"][name]))
        main = self.audits(self.content("Main.log"), p["main_audit_names"])
        self.require(len(library) == 252 and len(main) == 4
                     and proof["library_axiom_audits"] == library and proof["axiom_audits"] == main,
                     "recorded positive axiom audits differ")
        self.check(proof["main_check"], self.content("Main.log"), ["Main.lean"])
        elapsed, total = proof["import_build_seconds"], proof["total_seconds"]
        self.require(type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 600
                     and type(total) in (int, float) and math.isfinite(total) and elapsed <= total <= 600,
                     "aggregate source-build resource scope differs")
        if replay:
            result = self.read("replay.json")
            self.fields(result, {
                "status": "fresh-source-only-PTX-FFN-pipeline-proof-replay-passed",
                "recording_manifest_sha256": p["original_export_manifest_sha256"],
                "fresh_export_manifest_sha256": sha(self.content("proof-export-manifest.json")),
                "main_sha256": proof["main_sha256"], "main_regenerated_identically": True,
                "old_owned_olean_cache_used": False, "fresh_export_axiom_audits": main,
                "nvidia_execution": False, "original_paper_fully_reproduced": False,
            }, "fresh replay identity/scope differs")
            self.counters(result, {"owned_modules_freshly_compiled": 14, "positive_rechecks": 1,
                          "source_bound_proofs_added": 0, "model_calls": 0, "gpu_trials": 0,
                          "new_registered_source_certificates": 0}, "fresh replay counters differ")
            base = set(p["base_file_roster"]) - {"manifest.json"}
            self.require(self.read("proof-export-manifest.json") ==
                         {name: sha(self.content(name)) for name in base},
                         "fresh proof-export inventory differs")
        return {
            "status": "recorded-full-FFN-positive-evidence-validated",
            "pipeline_identity": proof["main_sha256"], "recorded_positive_checks": 1,
            "fresh_owned_modules_in_record": 14, "standard_axiom_audits": 256,
            "recorded_check_is_replay": replay, "fresh_Lean_checks": 0,
            "model_calls": 0, "GPU_trials": 0, "new_registered_source_certificates": 0,
            "original_paper_fully_reproduced": False,
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recording", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise ValueError("Fresh output required")
    result = Recording(args.recording).positive()
    output.mkdir(parents=True)
    (output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
