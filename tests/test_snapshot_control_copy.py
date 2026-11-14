"""Skipping overwritten containers must preserve every final replay input byte."""

import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

from reproduction.paper_results import snapshot_archives as storage
from reproduction.paper_results.check_snapshot_controls import (
    ControlArchive, ControlSnapshotCopies, rehash,
)
from reproduction.paper_results.snapshot_control_archives import ChunkedControlArchive


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def contents(root):
    return {p.relative_to(root).as_posix(): p.read_bytes() for p in root.rglob("*") if p.is_file()}


class ControlCopyEquivalenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-control-copy-equivalence-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.evidence = {"empty": b"", "value.bin": bytes(range(256)) * 4096,
                         "captured.py": b"raise RuntimeError('data; never executed')\n"}

    def baseline(self, schema):
        source = self.root / ("schema-" + str(schema))
        (source / "results").mkdir(parents=True)
        write(source / "results/audit.json", {"kind": "authored synthetic storage fixture"})
        (source / "results/RESULTS.md").write_text("Synthetic storage fixture; no claimed experiment.\n")
        # Matching basenames in metadata subdirectories must never be skipped.
        (source / "results/evidence.tar.gz").write_bytes(b"retained nested metadata")
        (source / "results/evidence-part-0001.tar.gz").write_bytes(b"retained nested part-name metadata")
        write(source / "evidence-manifest.json", {n: storage.digest(v) for n, v in self.evidence.items()})
        if schema == 2:
            layout = storage.build_parts(source, self.evidence)
            write(source / "evidence-layout.json", layout)
            binding = {"evidence_layout_sha256": storage.file_digest(source / "evidence-layout.json")}
            packed = ChunkedControlArchive(source)
        else:
            with tarfile.open(source / "evidence.tar.gz", mode="w:gz") as archive:
                for name, data in self.evidence.items():
                    info = tarfile.TarInfo(name)
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
            binding = {"evidence_archive_sha256": storage.file_digest(source / "evidence.tar.gz")}
            packed = ControlArchive(source / "evidence.tar.gz")
        write(source / "provenance.json", {"schema": schema, **binding,
            "evidence_manifest_sha256": storage.file_digest(source / "evidence-manifest.json")})
        return source, packed

    def equivalent_complete_rewrite(self, schema):
        source, packed = self.baseline(schema)
        original = contents(source)
        full, rewritten = self.root / "full-copy", self.root / "no-redundant-containers"
        shutil.copytree(source, full)
        copies = ControlSnapshotCopies(source)
        copies.copy(rewritten, rewrite_archive=True)
        self.assertTrue(all((full / name).is_file() for name in copies.archives))
        self.assertTrue(all(not (rewritten / name).exists() for name in copies.archives))
        self.assertEqual((rewritten / "results/evidence.tar.gz").read_bytes(), b"retained nested metadata")
        self.assertEqual((rewritten / "results/evidence-part-0001.tar.gz").read_bytes(),
                         b"retained nested part-name metadata")
        entries = packed.entries.copy()
        entries["value.bin"] = b"actual changed false-control bytes"
        entries["../retained-unsafe-control"] = b"unsafe logical data reaches the trusted reader"
        for destination in (full, rewritten):
            packed.write(destination, entries)
            rehash(destination, archive_changed=True)
        # Both complete snapshots contain exactly the same bytes, including
        # full payload containers and every updated manifest/provenance field.
        self.assertEqual(contents(full), contents(rewritten))
        self.assertEqual(contents(source), original)
        self.assertEqual(packed.entries, self.evidence)
        return source, rewritten, copies

    def test_schema_two_final_complete_inputs_are_byte_identical_after_the_full_rewrite(self):
        source, rewritten, _ = self.equivalent_complete_rewrite(2)
        layout = json.loads((rewritten / "evidence-layout.json").read_text())
        self.assertEqual(set(layout["logical_files"]), set(self.evidence) | {"../retained-unsafe-control"})
        self.assertEqual(layout["logical_files"]["../retained-unsafe-control"]["sha256"],
                         hashlib.sha256(b"unsafe logical data reaches the trusted reader").hexdigest())
        self.assertTrue((source / "evidence-part-0001.tar.gz").is_file())

    def test_legacy_final_complete_inputs_are_byte_identical_after_the_full_rewrite(self):
        source, rewritten, _ = self.equivalent_complete_rewrite(1)
        with tarfile.open(rewritten / "evidence.tar.gz") as archive:
            self.assertEqual({m.name for m in archive}, set(self.evidence) | {"../retained-unsafe-control"})
        self.assertTrue((source / "evidence.tar.gz").is_file())

    def test_report_only_controls_copy_every_container_and_metadata_byte(self):
        for schema in (1, 2):
            with self.subTest(schema=schema):
                source, _ = self.baseline(schema)
                target = self.root / ("report-only-" + str(schema))
                ControlSnapshotCopies(source).copy(target)
                self.assertEqual(contents(source), contents(target))

    def test_invalid_storage_schema_is_refused_before_copying_anything(self):
        source = self.root / "bad-schema"
        source.mkdir()
        write(source / "provenance.json", {"schema": True})
        with self.assertRaisesRegex(ValueError, "Supported source storage schema required"):
            ControlSnapshotCopies(source)


if __name__ == "__main__":
    unittest.main()
