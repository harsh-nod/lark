"""Lossless multi-part evidence storage and unchanged legacy entry guards."""

import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results import snapshot_archives as storage


class SnapshotArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lark-snapshot-parts-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.snapshot = self.root / "snapshot"
        self.snapshot.mkdir()

    def destination(self, name="out"):
        path = self.root / name
        path.mkdir()
        return path

    def example(self):
        content = {"evidence/a.bin": bytes(range(256)) * 2,
                   "evidence/code.py": b"raise RuntimeError('captured code must remain data')\n",
                   "evidence/empty": b""}
        layout = storage.build_parts(self.snapshot, content, chunk_bytes=128, tar_bytes=2048)
        return content, layout

    def test_real_oversized_logical_file_is_preserved_with_the_original_entry_limit(self):
        data = (bytes(range(256)) * (storage.MAX_ENTRY_BYTES // 256 + 1))[:storage.MAX_ENTRY_BYTES] + b"!"
        content = {"retained/history.tar.gz": data}
        layout = storage.build_parts(self.snapshot, content)
        entries = [r for archive in layout["archives"] for r in archive["entries"].values()]
        self.assertEqual([row["bytes"] for row in entries], [10_000_000, 1])
        destination = self.destination()
        storage.unpack_parts(self.snapshot, layout, destination,
                             expected_hashes={name: storage.digest(value) for name, value in content.items()})
        self.assertEqual((destination / "retained/history.tar.gz").read_bytes(), data)

    def test_multiple_parts_preserve_empty_files_and_code_bytes_without_execution(self):
        content, layout = self.example()
        self.assertGreater(len(layout["archives"]), 1)
        destination = self.destination()
        storage.unpack_parts(self.snapshot, layout, destination)
        self.assertEqual({p.relative_to(destination).as_posix(): p.read_bytes()
                          for p in destination.rglob("*") if p.is_file()}, content)

    def test_encoding_is_deterministic_and_independent_of_input_dictionary_order(self):
        content, first = self.example()
        other = self.root / "second"
        other.mkdir()
        second = storage.build_parts(other, dict(reversed(list(content.items()))), chunk_bytes=128, tar_bytes=2048)
        self.assertEqual(first, second)
        for part in first["archives"]:
            self.assertEqual((self.snapshot / part["path"]).read_bytes(), (other / part["path"]).read_bytes())

    def test_concatenated_gzip_control_stream_keeps_every_original_fragment(self):
        content, layout = self.example()
        for description in layout["archives"]:
            path = self.snapshot / description["path"]
            stream = gzip.decompress(path.read_bytes())
            path.write_bytes(b"".join(gzip.compress(stream[i:i+512], mtime=0)
                                     for i in range(0, len(stream), 512)))
            description.update(bytes=path.stat().st_size, sha256=storage.file_digest(path))
        destination = self.destination()
        storage.unpack_parts(self.snapshot, layout, destination)
        self.assertEqual({p.relative_to(destination).as_posix(): p.read_bytes()
                          for p in destination.rglob("*") if p.is_file()}, content)

    def test_missing_reordered_duplicated_and_boolean_fragment_metadata_are_refused(self):
        _, layout = self.example()
        missing = copy.deepcopy(layout)
        missing["archives"].pop()
        reordered = copy.deepcopy(layout)
        reordered["archives"].reverse()
        duplicate = copy.deepcopy(layout)
        first = next(iter(duplicate["archives"][0]["entries"].values()))
        duplicate["archives"][0]["entries"]["extra"] = copy.deepcopy(first)
        boolean = copy.deepcopy(layout)
        next(iter(boolean["archives"][0]["entries"].values()))["offset"] = False
        for altered in (missing, reordered, duplicate, boolean):
            with self.subTest(altered=altered), self.assertRaises(ValueError):
                storage.validate_layout(altered)

    def test_unsafe_paths_directory_collisions_and_entry_budget_overclaims_are_refused(self):
        _, layout = self.example()
        unsafe = copy.deepcopy(layout)
        name, row = unsafe["logical_files"].popitem()
        unsafe["logical_files"]["../" + name] = row
        collision = copy.deepcopy(layout)
        collision["logical_files"]["evidence"] = {"bytes": 0, "sha256": storage.digest(b"")}
        oversized = copy.deepcopy(layout)
        next(iter(oversized["archives"][0]["entries"].values()))["bytes"] = 10_000_001
        for altered in (unsafe, collision, oversized):
            with self.subTest(altered=altered), self.assertRaises(ValueError):
                storage.validate_layout(altered)

    def test_archive_mutation_and_coherently_changed_logical_hash_are_refused(self):
        content, layout = self.example()
        part = self.snapshot / layout["archives"][0]["path"]
        part.write_bytes(part.read_bytes() + b"changed")
        with self.assertRaisesRegex(ValueError, "Archive bytes differ"):
            storage.unpack_parts(self.snapshot, layout, self.destination())
        changed = copy.deepcopy(layout)
        changed["logical_files"]["evidence/a.bin"]["sha256"] = hashlib.sha256(b"wrong").hexdigest()
        with self.assertRaisesRegex(ValueError, "Logical evidence manifest differs"):
            storage.validate_layout(changed, {name: storage.digest(value) for name, value in content.items()})

    def test_forged_chunk_and_archive_hashes_still_require_the_full_logical_bytes(self):
        _, layout = self.example()
        description = layout["archives"][0]
        path = self.snapshot / description["path"]
        entries = []
        with tarfile.open(path) as archive:
            for member in archive:
                entries.append((member.name, archive.extractfile(member).read()))
        with tarfile.open(path, mode="w:gz") as archive:
            for index, (name, data) in enumerate(entries):
                data = (bytes([data[0] ^ 1]) + data[1:]) if index == 0 else data
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
                description["entries"][name]["sha256"] = storage.digest(data)
        description.update(bytes=path.stat().st_size, sha256=storage.file_digest(path))
        with self.assertRaisesRegex(ValueError, "Reassembled logical evidence differs"):
            storage.unpack_parts(self.snapshot, layout, self.destination())

    def test_existing_destination_and_existing_archive_are_never_overwritten(self):
        content, layout = self.example()
        with self.assertRaisesRegex(ValueError, "Fresh archive outputs required"):
            storage.build_parts(self.snapshot, content)
        destination = self.destination()
        marker = destination / "previous"
        marker.write_bytes(b"keep")
        with self.assertRaisesRegex(ValueError, "Fresh empty evidence destination required"):
            storage.unpack_parts(self.snapshot, layout, destination)
        self.assertEqual(marker.read_bytes(), b"keep")

    def test_legacy_single_entry_limit_remains_ten_million_bytes(self):
        path = self.snapshot / "legacy.tar.gz"
        data = b"a" * 10_000_001
        with tarfile.open(path, mode="w:gz") as archive:
            info = tarfile.TarInfo("too-big")
            info.size = len(data)
            archive.addfile(info, io.BytesIO(data))
        destination = self.destination()
        with self.assertRaisesRegex(ValueError, "Unexpected frozen entry"):
            replay.unpack(path, destination)
        self.assertFalse((destination / "too-big").exists())

    def test_snapshot_builder_binds_version_two_parts_to_the_complete_logical_manifest(self):
        (self.snapshot / "reproduction/results").mkdir(parents=True)
        (self.snapshot / "evidence").mkdir()
        paper_manifest = "reproduction/results/paper-source-manifest.json"
        (self.snapshot / paper_manifest).write_text("{}\n")
        (self.snapshot / "evidence/value").write_bytes(b"whole retained evidence")
        (self.snapshot / "auditor.py").write_bytes(b"# authored synthetic auditor; not executed\n")
        targets = {"storage_schema": 2, "evidence_commit": "a" * 40,
                   "evidence_groups": {"example": ["evidence/value", paper_manifest]},
                   "local_evidence": ["evidence/value", paper_manifest]}
        (self.snapshot / "targets.json").write_text(json.dumps(targets))
        with patch.object(replay, "ROOT", self.snapshot):
            replay.build(self.snapshot)
        self.assertFalse((self.snapshot / "evidence.tar.gz").exists())
        provenance = replay.read(self.snapshot / "provenance.json")
        self.assertEqual(provenance["schema"], 2)
        self.assertEqual(provenance["evidence_layout_sha256"],
                         storage.file_digest(self.snapshot / "evidence-layout.json"))
        destination = self.destination()
        storage.unpack_parts(self.snapshot, replay.read(self.snapshot / "evidence-layout.json"), destination,
                             expected_hashes=replay.read(self.snapshot / "evidence-manifest.json"))
        self.assertEqual((destination / "evidence/value").read_bytes(), b"whole retained evidence")
        self.assertEqual((destination / "reproduction/paper_results/audit.py").read_bytes(),
                         (self.snapshot / "auditor.py").read_bytes())

    def test_snapshot_builder_rejects_boolean_storage_schema_before_writing_archives(self):
        (self.snapshot / "targets.json").write_text(json.dumps({"storage_schema": True}))
        with patch.object(replay, "ROOT", self.snapshot), self.assertRaisesRegex(ValueError, "Unsupported storage schema"):
            replay.build(self.snapshot)
        self.assertEqual(list(self.snapshot.glob("*.tar.gz")), [])


if __name__ == "__main__":
    unittest.main()
