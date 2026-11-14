"""Earlier evidence bytes survive later runtime-helper edits at the same path."""

import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

from reproduction.paper_results.replay_snapshot import committed_evidence, preserved_origins


class PreservedEvidenceOriginsTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-preserved-evidence-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "-q", "--object-format=sha1")
        self.git("config", "user.name", "Synthetic evidence fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.name = "evidence/data.bin"
        path = self.root / self.name
        path.parent.mkdir()
        path.write_bytes(b"original recorded evidence\n")
        self.original = path.read_bytes()
        self.git("add", self.name)
        self.git("commit", "-qm", "original evidence")
        self.older = self.git("rev-parse", "HEAD")
        path.write_bytes(b"later runtime version\n")
        self.git("commit", "-qam", "later runtime")
        self.current = self.git("rev-parse", "HEAD")
        self.binding = {"commit": self.older, "sha256": hashlib.sha256(self.original).hexdigest()}

    def git(self, *args, data=None):
        return subprocess.check_output(["git", *args], input=data, cwd=self.root).decode().strip()

    def test_original_committed_bytes_and_path_survive_later_and_uncommitted_edits(self):
        (self.root / self.name).write_bytes(b"uncommitted filesystem content must not be captured\n")
        selected = preserved_origins({"preserved_evidence_origins": {self.name: self.binding}},
                                     {self.name}, set())
        data, origin = committed_evidence(self.name, self.current, selected, root=self.root)
        self.assertEqual(data, self.original)
        self.assertEqual(origin, {"kind": "git-blob", "commit": self.older, "path": self.name})
        current, _ = committed_evidence(self.name, self.current, {}, root=self.root)
        self.assertEqual(current, b"later runtime version\n")

    def test_changed_expected_bytes_are_refused(self):
        binding = {**self.binding, "sha256": "0" * 64}
        with self.assertRaisesRegex(ValueError, "Preserved evidence bytes differ"):
            committed_evidence(self.name, self.current, {self.name: binding}, root=self.root)

    def test_unrelated_commit_cannot_supply_earlier_evidence(self):
        tree = self.git("rev-parse", self.current + "^{tree}")
        unrelated = self.git("commit-tree", tree, data=b"unrelated synthetic history\n")
        binding = {**self.binding, "commit": unrelated}
        with self.assertRaisesRegex(ValueError, "not an ancestor"):
            committed_evidence(self.name, self.current, {self.name: binding}, root=self.root)

    def test_unused_local_definition_and_symbolic_origins_are_refused(self):
        for name, local, row in (
            ("undeclared", set(), self.binding),
            (self.name, {self.name}, self.binding),
            ("reproduction/paper_results/audit.py", set(), self.binding),
            (self.name, set(), {**self.binding, "commit": "HEAD"}),
            (self.name, set(), {**self.binding, "path": "another-file"}),
        ):
            with self.subTest(name=name, row=row), self.assertRaises(ValueError):
                preserved_origins({"preserved_evidence_origins": {name: row}},
                                  {self.name, "reproduction/paper_results/audit.py"}, local)


if __name__ == "__main__":
    unittest.main()
