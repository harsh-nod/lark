"""Preserve complete schema-two control bytes and reject them in trusted replay."""

from concurrent.futures import ThreadPoolExecutor
import errno
import gzip
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from reproduction.paper_results import snapshot_archives as storage
from reproduction.paper_results.check_snapshot_controls import control_archive, rehash
from reproduction.paper_results.snapshot_control_archives import ChunkedControlArchive


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


class ChunkedControlArchiveTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-chunked-control-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.content = {"empty": b"", "evidence/data": bytes(range(256)) * 3,
                        "nested/" + "long-name-" * 25 + ".py": b"raise RuntimeError('captured code is data')\n"}
        self.source = self.root / "source"
        self.source.mkdir()

    def baseline(self, content=None):
        content = self.content if content is None else content
        layout = storage.build_parts(self.source, content)
        write(self.source / "evidence-layout.json", layout)
        write(self.source / "evidence-manifest.json", {n: storage.digest(v) for n, v in content.items()})
        write(self.source / "provenance.json", {
            "schema": 2, "evidence_layout_sha256": storage.file_digest(self.source / "evidence-layout.json"),
            "evidence_manifest_sha256": storage.file_digest(self.source / "evidence-manifest.json")})
        return layout

    def destination(self, name):
        path = self.root / name
        path.mkdir()
        return path

    def restored(self, snapshot):
        output = Path(tempfile.mkdtemp(prefix="restored-", dir=self.root))
        layout = json.loads((snapshot / "evidence-layout.json").read_text())
        hashes = json.loads((snapshot / "evidence-manifest.json").read_text())
        storage.unpack_parts(snapshot, layout, output, expected_hashes=hashes)
        return {p.relative_to(output).as_posix(): p.read_bytes() for p in output.rglob("*") if p.is_file()}

    def test_complete_multipart_roundtrip_with_empty_code_and_long_logical_names(self):
        self.baseline()
        packed = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=1024)
        self.addCleanup(packed.close)
        output = self.destination("complete")
        layout = packed.write(output, packed.entries.copy())
        self.assertGreater(len(layout["archives"]), 1)
        self.assertEqual(self.restored(output), self.content)
        self.assertEqual(packed.entries, self.content)

    def test_real_ten_million_and_one_byte_file_keeps_both_bounded_fragments(self):
        content = {"whole-original.bin": b"z" * 10_000_001}
        self.baseline(content)
        packed = ChunkedControlArchive(self.source)
        self.addCleanup(packed.close)
        output = self.destination("large")
        layout = packed.write(output, packed.entries.copy())
        fragments = [row for part in layout["archives"] for row in part["entries"].values()]
        self.assertEqual([row["bytes"] for row in fragments], [10_000_000, 1])
        self.assertEqual(self.restored(output), content)

    def test_unsafe_logical_control_and_all_original_bytes_reach_the_trusted_reader(self):
        self.baseline()
        packed = ChunkedControlArchive(self.source)
        self.addCleanup(packed.close)
        entries = packed.entries.copy()
        unsafe = "../escaped-control-marker"
        entries[unsafe] = b"preserved unsafe control bytes"
        entries["evidence/data"] = b"changed control data"
        output = self.destination("unsafe")
        layout = packed.write(output, entries)
        self.assertEqual(set(layout["logical_files"]), set(entries))
        self.assertEqual(layout["logical_files"][unsafe]["sha256"], storage.digest(entries[unsafe]))
        retained = []
        for part in layout["archives"]:
            # Read actual physical bytes without applying logical path mapping.
            stream = gzip.decompress((output / part["path"]).read_bytes())
            with tarfile.open(fileobj=io.BytesIO(stream), mode="r:") as archive:
                for member in archive:
                    self.assertNotIn("..", Path(member.name).parts)
                    if part["entries"][member.name]["file"] == unsafe:
                        retained.append(archive.extractfile(member).read())
        self.assertEqual(b"".join(retained), entries[unsafe])
        target = self.destination("refused")
        with self.assertRaisesRegex(ValueError, "Unsafe evidence path"):
            storage.unpack_parts(output, layout, target)
        self.assertEqual(list(target.iterdir()), [])
        self.assertFalse((self.root / "escaped-control-marker").exists())
        self.assertEqual(packed.entries, self.content)

    def test_two_independent_workers_keep_every_baseline_member_and_their_own_mutation(self):
        self.baseline()
        packed = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=2048)
        self.addCleanup(packed.close)

        def build(index):
            output = self.destination(str(index))
            entries = packed.entries.copy()
            entries["case.json"] = str(index).encode()
            packed.write(output, entries)
            return output, entries

        with ThreadPoolExecutor(max_workers=2) as pool:
            outputs = list(pool.map(build, range(2)))
        for output, entries in outputs:
            self.assertEqual(self.restored(output), entries)
        self.assertEqual(packed.entries, self.content)

    def test_reordered_dictionary_and_reused_immutable_fragments_are_deterministic(self):
        self.baseline()
        packed = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=2048)
        self.addCleanup(packed.close)
        left, right = self.destination("left"), self.destination("right")
        packed.write(left, packed.entries.copy())
        packed.write(right, dict(reversed(list(packed.entries.items()))))
        self.assertEqual({p.name: p.read_bytes() for p in left.iterdir()},
                         {p.name: p.read_bytes() for p in right.iterdir()})

    def test_shared_complete_parts_survive_copy_on_write_and_changed_part_boundaries(self):
        content = {"a": b"A" * 128, "b": b"B" * 128, "c": b"C" * 128}
        self.baseline(content)
        packed = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=1024)
        self.addCleanup(packed.close)
        left, right = self.destination("left"), self.destination("right")
        original_layout = packed.write(left, packed.entries.copy())
        original_files = {p.name: p.read_bytes() for p in left.iterdir()}
        packed.write(right, packed.entries.copy())
        for part in original_layout["archives"]:
            self.assertTrue((left / part["path"]).samefile(right / part["path"]))
            self.assertFalse((left / part["path"]).is_symlink())

        # Growing b creates a new fragment and moves c to another physical part.
        # Rewriting left must preserve the complete, independent right snapshot.
        changed = {**packed.entries, "b": b"changed" * 20}
        changed_layout = packed.write(left, changed)
        self.assertGreater(len(changed_layout["archives"]), len(original_layout["archives"]))
        self.assertEqual(self.restored(left), changed)
        self.assertEqual(self.restored(right), content)
        self.assertEqual({p.name: p.read_bytes() for p in right.iterdir()}, original_files)

        # Replacing shared files again must leave the private baseline reusable.
        packed.write(left, packed.entries.copy())
        self.assertEqual(self.restored(left), content)
        self.assertEqual({p.name: p.read_bytes() for p in left.iterdir()}, original_files)
        packed.close()
        self.assertEqual(self.restored(right), content)

    def test_unavailable_hard_links_fall_back_to_complete_regular_file_bytes(self):
        self.baseline()
        packed = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=1024)
        self.addCleanup(packed.close)
        output = self.destination("copy-fallback")
        with patch("reproduction.paper_results.snapshot_control_archives.os.link",
                   side_effect=OSError(errno.EXDEV, "Synthetic cross-device link refusal")):
            layout = packed.write(output, packed.entries.copy())
        self.assertTrue(all((output / row["path"]).is_file() for row in layout["archives"]))
        self.assertEqual(self.restored(output), self.content)

    def test_obsolete_copied_parts_are_removed_without_dropping_any_logical_byte(self):
        self.baseline()
        output = self.destination("rewritten")
        first = ChunkedControlArchive(self.source, chunk_bytes=128, tar_bytes=1024)
        self.addCleanup(first.close)
        first_layout = first.write(output, first.entries.copy())
        second = ChunkedControlArchive(self.source, chunk_bytes=1024, tar_bytes=4096)
        self.addCleanup(second.close)
        second_layout = second.write(output, second.entries.copy())
        self.assertGreater(len(first_layout["archives"]), len(second_layout["archives"]))
        self.assertEqual({p.name for p in output.glob("evidence-part-*.tar.gz")},
                         {part["path"] for part in second_layout["archives"]})
        self.assertEqual(self.restored(output), self.content)

    def test_corrupt_baseline_is_refused_before_building_compression_cache(self):
        layout = self.baseline()
        path = self.source / layout["archives"][0]["path"]
        path.write_bytes(path.read_bytes() + b"changed")
        with self.assertRaisesRegex(ValueError, "Archive bytes differ"):
            ChunkedControlArchive(self.source)

    def test_factory_selects_schema_two_and_rehash_binds_complete_layout_and_manifest(self):
        self.baseline()
        packed = control_archive(self.source)
        self.addCleanup(packed.close)
        self.assertIsInstance(packed, ChunkedControlArchive)
        packed.write(self.source, packed.entries.copy())
        results = self.source / "results"
        results.mkdir()
        write(results / "audit.json", {"kind": "authored synthetic fixture; no claimed experiment"})
        (results / "RESULTS.md").write_text("Synthetic metadata fixture.\n")
        rehash(self.source, archive_changed=True)
        provenance = json.loads((self.source / "provenance.json").read_text())
        self.assertEqual(provenance["evidence_layout_sha256"],
                         storage.file_digest(self.source / "evidence-layout.json"))
        self.assertEqual(provenance["evidence_manifest_sha256"],
                         storage.file_digest(self.source / "evidence-manifest.json"))
        self.assertNotIn("evidence_archive_sha256", provenance)
        self.assertEqual(self.restored(self.source), self.content)


if __name__ == "__main__":
    unittest.main()
