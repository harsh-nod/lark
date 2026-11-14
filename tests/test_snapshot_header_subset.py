"""Verified refusal headers cannot replace complete evidence validation."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results import snapshot_archives as storage

ROOT = Path(__file__).resolve().parents[1]


class HeaderSubsetTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-header-subset-tests-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.snapshot = self.root / "snapshot"
        self.snapshot.mkdir()
        self.content = {"a/header.json": b'{"valid":true}\n',
                        "b/packet.tar.gz": bytes(range(256)) * 3,
                        "c/empty": b""}
        self.layout = storage.build_parts(self.snapshot, self.content, chunk_bytes=128, tar_bytes=2048)

    def destination(self, name):
        target = self.root / name
        target.mkdir()
        return target

    def subset(self, name, selected, layout=None):
        target = self.destination(name)
        storage.unpack_header_files(self.snapshot, self.layout if layout is None else layout,
                                    target, selected)
        return target

    def test_cross_part_and_empty_selected_files_keep_exact_bytes(self):
        selected = {"b/packet.tar.gz", "c/empty"}
        target = self.subset("selected", selected)
        self.assertEqual({p.relative_to(target).as_posix(): p.read_bytes()
                          for p in target.rglob("*") if p.is_file()},
                         {name: self.content[name] for name in selected})
        self.assertFalse((target / "a/header.json").exists())

    def test_unselected_physical_part_is_freshly_hashed_after_previous_header_success(self):
        self.subset("first", {"a/header.json"})
        description = next(row for row in self.layout["archives"]
                           if all(r["file"] != "a/header.json" for r in row["entries"].values()))
        path = self.snapshot / description["path"]
        data = path.read_bytes()
        path.write_bytes(bytes([data[0] ^ 1]) + data[1:])
        with self.assertRaisesRegex(ValueError, "Archive bytes differ"):
            self.subset("second", {"a/header.json"})

    def test_selected_logical_and_fragment_bindings_are_both_required(self):
        for binding in ("logical", "fragment"):
            layout = copy.deepcopy(self.layout)
            if binding == "logical":
                layout["logical_files"]["a/header.json"]["sha256"] = "0" * 64
            else:
                fragment = next(r for a in layout["archives"] for r in a["entries"].values()
                                if r["file"] == "a/header.json")
                fragment["sha256"] = "0" * 64
            gate = "Reassembled logical evidence differs" if binding == "logical" else "Archive fragment bytes differ"
            with self.subTest(binding=binding), self.assertRaisesRegex(ValueError, gate):
                self.subset(binding, {"a/header.json"}, layout)

    def test_subset_success_cannot_certify_an_unchecked_logical_packet(self):
        layout = copy.deepcopy(self.layout)
        layout["logical_files"]["b/packet.tar.gz"]["sha256"] = "0" * 64
        self.subset("headers-consistent", {"a/header.json"}, layout)
        with self.assertRaisesRegex(ValueError, "Reassembled logical evidence differs"):
            storage.unpack_parts(self.snapshot, layout, self.destination("complete-must-refuse"))

    def test_missing_or_empty_header_roster_is_refused(self):
        for name, selected in (("missing", {"missing"}), ("empty", set())):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "Declared nonempty header selection"):
                self.subset(name, selected)

    def test_unselected_unsafe_logical_path_is_still_refused(self):
        layout = copy.deepcopy(self.layout)
        layout["logical_files"]["../outside"] = layout["logical_files"].pop("c/empty")
        for archive in layout["archives"]:
            for row in archive["entries"].values():
                if row["file"] == "c/empty":
                    row["file"] = "../outside"
        with self.assertRaisesRegex(ValueError, "Unsafe evidence path"):
            self.subset("unsafe", {"a/header.json"}, layout)
        self.assertFalse((self.root / "outside").exists())

    def test_v28_selection_contains_frozen_definitions_and_no_proof_archives(self):
        snapshot = ROOT / "reproduction/paper_results/snapshots/20261114-v28"
        layout = json.loads((snapshot / "evidence-layout.json").read_text())
        config = json.loads((snapshot / "targets.json").read_text())
        selected = replay.preflight_header_paths(layout, config)
        self.assertIn("reproduction/paper_results/audit.py", selected)
        self.assertIn("reproduction/paper_results/targets.json", selected)
        self.assertIn("reproduction/paper_results/ptx_ffn_release_protocol.json", selected)
        self.assertTrue(all(not n.endswith((".tar.gz", ".whl", ".olean")) for n in selected))
        spec = config["ptx_ffn_proof"]
        self.assertIn(spec["ci_job_prefix"] + "/logs.raw", selected)
        self.assertIn(spec["publication_prefix"] + "/downloads.json", selected)
        self.assertLess(sum(layout["logical_files"][n]["bytes"] for n in selected), 10_000_000)


class HeaderExecutionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-header-execution-tests-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.script = self.root / "audit.py"
        self.script.write_text("# Authored refusal-path fixture; no experiment.\n")
        self.digest = storage.file_digest(self.script)

    def test_header_mode_never_executes_the_complete_auditor(self):
        with patch.object(sys, "path", sys.path[:]), \
                patch.object(replay, "preflight_frozen_release_headers") as check, \
                patch.object(replay.runpy, "run_path") as complete:
            replay.run_frozen_headers(self.script, self.digest)
            replay.run_frozen_headers(self.script, self.digest)
        self.assertEqual(check.call_count, 2)
        complete.assert_not_called()

    def test_missing_partial_input_falls_through_but_known_refusal_propagates(self):
        for error in (FileNotFoundError("not in partial view"), ValueError("unknown partial format")):
            with self.subTest(error=error), patch.object(sys, "path", sys.path[:]), \
                    patch.object(replay, "preflight_frozen_release_headers", side_effect=error):
                self.assertIsNone(replay.run_frozen_headers(self.script, self.digest))
        with patch.object(sys, "path", sys.path[:]), \
                patch.object(replay, "preflight_frozen_release_headers",
                             side_effect=ValueError("PTX ffn actual source CI differs")), \
                self.assertRaisesRegex(ValueError, "PTX ffn actual source CI differs"):
            replay.run_frozen_headers(self.script, self.digest)

    def test_forged_auditor_digest_prevents_any_header_execution(self):
        with patch.object(replay, "preflight_frozen_release_headers") as check, \
                self.assertRaisesRegex(ValueError, "Frozen auditor bytes differ"):
            replay.run_frozen_headers(self.script, "0" * 64)
        check.assert_not_called()

    def test_passing_preflight_unconditionally_repeats_complete_unpack_each_time(self):
        snapshot = self.root / "snapshot"
        snapshot.mkdir()
        config = {"ptx_ffn_proof": {}}
        replay.write(snapshot / "targets.json", config)
        (snapshot / "auditor.py").write_bytes(self.script.read_bytes())
        content = {"reproduction/paper_results/audit.py": self.script.read_bytes(),
                   "reproduction/paper_results/targets.json": (snapshot / "targets.json").read_bytes()}
        layout = storage.build_parts(snapshot, content)
        replay.write(snapshot / "evidence-layout.json", layout)
        replay.write(snapshot / "evidence-manifest.json", {n: storage.digest(v) for n, v in content.items()})
        replay.write(snapshot / "provenance.json", {
            "schema": 2,
            "evidence_layout_sha256": storage.file_digest(snapshot / "evidence-layout.json"),
            "evidence_manifest_sha256": storage.file_digest(snapshot / "evidence-manifest.json"),
        })
        replay.write(snapshot / "manifest.json", {p.name: storage.file_digest(p) for p in snapshot.iterdir()})
        events = []

        def full_unpack(*args, **kwargs):
            events.append("fresh-full-unpack")
            raise RuntimeError("complete unpack reached; fixture deliberately stops here")

        with patch.object(replay, "preflight_schema2_headers", side_effect=lambda *args: events.append("headers")), \
                patch.object(storage, "unpack_parts", side_effect=full_unpack):
            for _ in range(2):
                with self.assertRaisesRegex(RuntimeError, "complete unpack reached"):
                    replay.replay(snapshot, self.root / "unused-manuscript.tar")
        self.assertEqual(events, ["headers", "fresh-full-unpack", "headers", "fresh-full-unpack"])


if __name__ == "__main__":
    unittest.main()
