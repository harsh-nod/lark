"""Read the complete recorded FFN packet without executing captured code.

All archives are decoded and every member is hashed on each invocation. The
recorded Lean checks, refusals and wheel are evidence, not new proof executions.
"""

import argparse
import io
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
import zipfile

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from ptx_ffn_evidence import Recording, same_json, sha


def subtree(entries, prefix):
    return {name[len(prefix):]: data for name, data in entries.items() if name.startswith(prefix)}


class Packet(Recording):
    def __init__(self, root, protocol=None):
        super().__init__(root, protocol, max_file_bytes=90_000_000)
        self.spec = self.protocol["packet"]

    def recording(self, entries):
        return Recording(protocol=self.protocol, entries=entries)

    def archive(self, label, row):
        expected = self.spec["archives"][label]
        self.require(type(row) is dict and set(row) == {
            "group", "files", "uncompressed_bytes", "archive_bytes", "archive_sha256", "inventory_sha256"},
            "archive metadata roster differs")
        self.fields(row, expected, "archive group/count/size differs")
        data, inventory_data = self.content(label + ".tar.gz"), self.content(label + "-files.json")
        self.counters(row, {"archive_bytes": len(data)}, "archive byte count differs")
        self.require(sha(data) == row["archive_sha256"] and sha(inventory_data) == row["inventory_sha256"]
                     and expected["uncompressed_bytes"] <= 85_000_000, "archive binding/bounds differ")
        inventory = json.loads(inventory_data)
        self.require(type(inventory) is dict and len(inventory) == expected["files"],
                     "archive member roster differs")
        for name, bound in inventory.items():
            self.require(type(name) is str and bool(name), "archive member path required")
            path = PurePosixPath(name)
            self.require(bool(path.parts) and str(path) == name and not path.is_absolute()
                         and ".." not in path.parts, "unsafe archive path")
            self.require(type(bound) is dict and set(bound) == {"bytes", "sha256"}
                         and type(bound["bytes"]) is int and 0 <= bound["bytes"] <= 10_000_000
                         and type(bound["sha256"]) is str
                         and re.fullmatch(r"[0-9a-f]{64}", bound["sha256"]) is not None,
                         "archive member binding/bounds differ")
        entries, size = {}, 0
        with tarfile.open(fileobj=io.BytesIO(data), mode="r|gz") as stream:
            for member in stream:
                self.require(member.isfile() and member.name in inventory and member.name not in entries,
                             "unexpected or nonregular archive member")
                bound = inventory[member.name]
                size += member.size
                self.require(member.size == bound["bytes"] and size <= expected["uncompressed_bytes"]
                             and len(entries) < expected["files"], "archive member size differs")
                value = stream.extractfile(member).read()
                self.require(len(value) == member.size and sha(value) == bound["sha256"],
                             "archive actual member bytes differ")
                entries[member.name] = value
        self.require(set(entries) == set(inventory) and size == expected["uncompressed_bytes"],
                     "incomplete archive members")
        return entries

    def direct_controls(self, entries, export):
        reader = self.recording(entries)
        reader.inventory()
        report = reader.read("results.json")
        self.fields(report, self.spec["direct_fields"], "direct-control scope/counters differ")
        self.require(report["driver_sha256"] == sha(entries["driver.py"]), "direct-control driver differs")
        replay = subtree(entries, "positive-source-only-replay/")
        positive = self.recording(replay).positive()
        self.require(same_json(report["positive_replay"], json.loads(replay["replay.json"])),
                     "direct-control positive replay differs")
        specs = self.spec["direct_controls"]
        self.require(type(report["negative_controls"]) is list
                     and len(report["negative_controls"]) == len(specs), "direct-control roster differs")
        for row, spec in zip(report["negative_controls"], specs, strict=True):
            self.fields(row, spec["fields"], "direct-control identity/scope differs")
            part = subtree(entries, row["control"] + "/")
            case = self.recording(part)
            self.require(case.inventory() == set(spec["files"]), "direct-control file roster differs")
            self.require(same_json(case.read("results.json"), row), "direct-control result differs")
            filename = spec["command"][0]
            source, log = part[filename], part["Lean.log"]
            self.require(sha(source) == row["source_sha256"]
                         and row["input_bindings"] == {n: sha(part[n]) for n in self.protocol["positive_fields"]["input_bindings"]},
                         "direct-control actual source/input binding differs")
            for name in ("bypass.json", "translation.json", "scope.json"):
                if name + "_sha256" in spec:
                    self.require(sha(part[name]) == spec[name + "_sha256"], "direct-control captured preparation differs")
            if "bypass.json" in part:
                bypass = case.read("bypass.json")
                original = (export["Main.lean"] if filename == "Main.lean" else
                            export["owned-sources/lean/Lark/PtxFeedForwardPipeline.lean"])
                before, after = bypass["before"].encode(), bypass["after"].encode()
                self.require(bypass["all_input_bytes_unchanged"] is True and original.count(before) == 1
                             and source == original.replace(before, after)
                             and all(part[n] == export[n] for n in row["input_bindings"]),
                             "direct proof-dependency bypass differs")
            self.check(row["Lean"], log, spec["command"], accepted=False)
            lines = source.decode().splitlines()
            first = [i + 1 for i, line in enumerate(lines) if line.startswith("theorem " + row["expected_gate"] + " ")]
            self.require(len(first) == 1, "direct-control theorem gate missing")
            last = next((i + 1 for i, line in enumerate(lines) if i + 1 > first[0]
                         and line.startswith("theorem ")), len(lines)) - 1
            errors = [int(n) for n in re.findall(re.escape(filename.encode()) + rb":([0-9]+):[0-9]+: error:", log)]
            self.require(same_json(row["expected_lines"], [first[0], last])
                         and any(first[0] <= n <= last for n in errors)
                         and not any(marker in log.lower() for marker in (
                             b"stack overflow", b"maximum recursion", b"maximum number of heartbeats",
                             b"maximum heartbeats", b"deep recursion")), "direct Lean refusal gate/resource differs")
        return positive

    def false_controls(self, entries, rows, seen):
        names = {name.split("/", 1)[0] for name in entries}
        self.require(names <= set(rows) and not names.intersection(seen), "false-control archive roster differs")
        results = []
        for name in sorted(names):
            part = subtree(entries, name + "/")
            case = self.recording(part)
            self.require(case.inventory() == {"manifest.json", "results.json"} | {
                "recording/" + n for n in self.protocol["base_file_roster"]},
                "complete false-control payload roster differs")
            row = case.read("results.json")
            self.require(same_json(row, rows[name]), "SDK refusal transcript differs")
            false = self.recording(subtree(part, "recording/"))
            false.inventory()
            self.require(row["complete_false_recording_manifest_sha256"] == sha(false.content("manifest.json")),
                         "false-control recording binding differs")
            self.fields(row, {"status": "rejected-before-fresh-Lean-work", "output_created": False},
                        "false-control refusal scope differs")
            self.require(type(row["detail"]) is str and bool(row["detail"])
                         and "inventory" not in row["detail"].lower(), "SDK refusal was not semantic")
            try:
                false.positive()
            except ValueError as exc:
                gate = str(exc)
                self.require("inventory" not in gate.lower(), "independent refusal was only an inventory mismatch")
            else:
                self.require(False, "coherently rehashed false recording accepted")
            results.append({"case": name, "independent_refusal": gate})
        seen.update(names)
        return results

    def wheel(self, entries):
        reader = self.recording(entries)
        # The producer packet includes every file listed by the wheel's original
        # manifest, rather than that manifest itself. Keep its original inventory
        # separately pinned; do not invent an inner manifest or omit its files.
        self.require(same_json({n: sha(b) for n, b in entries.items()},
                               self.spec["wheel_original_inventory"]),
                     "complete original wheel evidence inventory differs")
        report, build = reader.read("results.json"), reader.read("build-results.json")
        self.fields(report, self.spec["wheel_fields"], "installed-wheel scope/probe differs")
        self.fields(build, self.spec["wheel_build_fields"], "offline wheel build scope differs")
        self.require(same_json(report["build"], build)
                     and same_json(report["installed_probe"], json.loads(entries["installed-path-and-bindings.stdout"])),
                     "installed-wheel captured summaries differ")
        replay = subtree(entries, "fresh-installed-replay/")
        positive = self.recording(replay).positive()
        self.require(same_json(report["replay"], json.loads(replay["replay.json"])), "installed replay differs")
        elapsed = report["replay_seconds"]
        self.require(type(elapsed) in (int, float) and math.isfinite(elapsed)
                     and json.loads(replay["results.json"])["total_seconds"] <= elapsed <= 600,
                     "installed replay resource scope differs")
        wheel = entries[build["wheel_filename"]]
        self.counters(build, {"wheel_bytes": len(wheel)}, "wheel byte count differs")
        self.require(sha(wheel) == build["wheel_sha256"], "actual wheel hash differs")
        with zipfile.ZipFile(io.BytesIO(wheel)) as archive:
            infos = archive.infolist()
            self.require(len(infos) == len({i.filename for i in infos})
                         and all(0 <= i.file_size <= 10_000_000 for i in infos)
                         and sum(i.file_size for i in infos) <= 85_000_000, "wheel entries/bounds differ")
            names = set(archive.namelist())
            for name, digest in self.protocol["source_bindings"].items():
                path = "lark_kernels/" + name[7:] if name.startswith("python/") else None
                if path is None:
                    matches = [n for n in names if n.endswith("/share/lark/" + name)]
                    self.require(len(matches) == 1, "wheel Lean source roster differs")
                    path = matches[0]
                self.require(path in names and sha(archive.read(path)) == digest
                             == sha(replay["owned-sources/" + name]), "wheel/installed-replay source bytes differ")
        return positive

    def packet(self):
        paths = self.inventory()
        self.require(sha(self.content("manifest.json")) == self.spec["manifest_sha256"],
                     "separately pinned complete packet manifest differs")
        report = self.read("results.json")
        self.fields(report, self.spec["fields"], "complete packet scope/counters differ")
        self.require(type(report["archives"]) is dict and set(report["archives"]) == set(self.spec["archives"]),
                     "complete archive roster differs")
        expected = {"manifest.json", "results.json", "packaging-driver.py"}
        for label in report["archives"]:
            expected.update((label + ".tar.gz", label + "-files.json"))
        self.require(paths == expected, "packet file roster differs")
        export = self.archive("export", report["archives"]["export"])
        positives = [self.recording(export).positive()]
        direct = self.archive("source-controls-and-fresh-replay", report["archives"]["source-controls-and-fresh-replay"])
        positives.append(self.direct_controls(direct, export))
        del direct, export
        installed = self.archive("installed-wheel-and-fresh-replay", report["archives"]["installed-wheel-and-fresh-replay"])
        positives.append(self.wheel(installed))
        del installed
        meta = self.archive("false-recordings-metadata", report["archives"]["false-recordings-metadata"])
        self.require(set(meta) == {"manifest.json", "results.json", "partial-results.json", "driver.py"},
                     "false-control history metadata roster differs")
        false_report = json.loads(meta["results.json"])
        self.fields(false_report, {"status": "all31-coherently-rehashed-FFN-controls-rejected",
                    "all_false_payloads_retained": True, "original_paper_fully_reproduced": False},
                    "false-control scope differs")
        self.counters(false_report, {"negative_controls": 31, "fresh_Lean_checks": 0, "GPU_trials": 0,
                      "model_calls": 0, "source_bound_proofs_added": 0, "new_registered_source_certificates": 0},
                      "false-control counters differ")
        self.require(same_json(false_report["checks"], self.spec["false_controls"]),
                     "complete false-control transcript roster differs")
        rows = {r["name"]: r for r in false_report["checks"]}
        original_inventory = json.loads(meta["manifest.json"])
        actual_inventory = {n: sha(b) for n, b in meta.items() if n != "manifest.json"}
        seen, negatives = set(), []
        for label in report["archives"]:
            if label.startswith("false-recordings-") and label != "false-recordings-metadata":
                entries = self.archive(label, report["archives"][label])
                self.require(not set(entries).intersection(actual_inventory), "false-control duplicate file")
                actual_inventory.update({n: sha(b) for n, b in entries.items()})
                negatives.extend(self.false_controls(entries, rows, seen))
                del entries
        self.require(seen == set(rows) and same_json(actual_inventory, original_inventory),
                     "complete retained false-control inventory differs")
        identities = {p["pipeline_identity"] for p in positives}
        self.require(len(identities) == 1, "replays counted as distinct pipelines")
        return {
            "status": "complete-recorded-FFN-packet-semantics-validated",
            "packet_manifest_sha256": self.spec["manifest_sha256"], "archives_checked": 15,
            "archive_members_checked": sum(r["files"] for r in report["archives"].values()),
            "uncompressed_member_bytes_checked": sum(r["uncompressed_bytes"] for r in report["archives"].values()),
            "recorded_positive_checks": positives, "distinct_recorded_pipeline_identities": sorted(identities),
            "recorded_direct_Lean_refusals": 4, "independent_false_recording_refusals": negatives,
            "wheel_owned_sources_byte_checked": 72, "captured_code_executed": False,
            "fresh_Lean_checks": 0, "model_calls": 0, "GPU_trials": 0,
            "new_registered_source_certificates": 0, "original_paper_fully_reproduced": False,
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise ValueError("Fresh output required")
    result = Packet(args.packet).packet()
    output.mkdir(parents=True)
    (output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "archives_checked", "archive_members_checked")}), flush=True)


if __name__ == "__main__":
    main()
