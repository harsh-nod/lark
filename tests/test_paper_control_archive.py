"""The control archive preserves the complete byte stream consumed by replay."""

from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from reproduction.paper_results.check_snapshot_controls import ControlArchive


class PaperControlArchiveTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-control-archive-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.entries = {
            "empty": b"",
            "unchanged.bin": bytes(range(256)) * 6,
            "nested/" + "long-name-" * 24 + ".json": b'{"original": true}\n',
        }
        source = self.root / "source.tar.gz"
        with tarfile.open(source, "w:gz") as archive:
            for name, data in self.entries.items():
                info = tarfile.TarInfo(name)
                info.size = len(data)
                archive.addfile(info, io.BytesIO(data))
        self.packed = ControlArchive(source)

    def read_output(self, directory):
        path = directory / "evidence.tar.gz"
        # Check both ordinary gzip decoding and the public tar reader.
        stream = gzip.decompress(path.read_bytes())
        with tarfile.open(fileobj=io.BytesIO(stream), mode="r:") as archive:
            values = {member.name: archive.extractfile(member).read() for member in archive}
        with tarfile.open(path) as archive:
            self.assertEqual([member.name for member in archive], list(values))
        recorded = json.loads((directory / "evidence-manifest.json").read_text())
        self.assertEqual(recorded, {
            name: hashlib.sha256(data).hexdigest() for name, data in values.items()})
        return values

    def test_complete_roundtrip_including_empty_and_long_pax_names(self):
        self.packed.write(self.root, self.packed.entries.copy())
        self.assertEqual(self.read_output(self.root), self.entries)

    def test_changed_and_added_unsafe_member_are_preserved_for_replay_to_reject(self):
        entries = self.packed.entries.copy()
        entries["unchanged.bin"] = b"changed data"
        entries["../must-be-rejected-by-replay"] = b"retained malicious control"
        self.packed.write(self.root, entries)
        self.assertEqual(self.read_output(self.root), entries)
        self.assertEqual(self.packed.entries, self.entries)
        self.assertFalse((self.root.parent / "must-be-rejected-by-replay").exists())

    def test_two_independent_control_outputs_and_deterministic_baseline(self):
        def build(index):
            output = self.root / str(index)
            output.mkdir()
            entries = self.packed.entries.copy()
            entries["case.json"] = str(index).encode()
            self.packed.write(output, entries)
            return output, entries
        with ThreadPoolExecutor(max_workers=2) as pool:
            outputs = list(pool.map(build, range(2)))
        for output, entries in outputs:
            self.assertEqual(self.read_output(output), entries)
        baseline = self.root / "baseline"
        baseline.mkdir()
        self.packed.write(self.root, self.packed.entries.copy())
        self.packed.write(baseline, self.packed.entries.copy())
        self.assertEqual((self.root / "evidence.tar.gz").read_bytes(),
                         (baseline / "evidence.tar.gz").read_bytes())
        self.assertEqual(self.packed.entries, self.entries)


if __name__ == "__main__":
    unittest.main()
