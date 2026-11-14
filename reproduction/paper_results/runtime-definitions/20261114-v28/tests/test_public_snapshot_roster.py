"""Pin all anonymous-download inputs to Git, independent of working-tree files."""

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from reproduction.paper_results.check_public_snapshot import ROOT, expected_counts, published_paths


class PublicSnapshotRosterTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-public-roster-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "--quiet")
        self.relative = Path("reproduction/paper_results")
        self.snapshot = self.relative / "snapshots/test-frozen-version"
        (self.root / self.relative).mkdir(parents=True)
        for name in ("replay_snapshot.py", "check_snapshot_controls.py",
                     "snapshot_archives.py", "snapshot_control_archives.py"):
            (self.root / self.relative / name).write_text("# Authored roster fixture; never executed.\n")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def commit(self, schema, parts=()):
        snapshot = self.root / self.snapshot
        if snapshot.exists():
            shutil.rmtree(snapshot)
        (snapshot / "results").mkdir(parents=True)
        for name in ("auditor.py", "targets.json", "evidence-manifest.json", "results/audit.json",
                     "results/RESULTS.md", "results/manifest.json"):
            (snapshot / name).write_text("Authored synthetic roster data; never replayed.\n")
        (snapshot / "provenance.json").write_text(json.dumps({"schema": schema}))
        if schema == 1 and type(schema) is int:
            (snapshot / "evidence.tar.gz").write_bytes(b"synthetic legacy archive bytes")
        else:
            (snapshot / "evidence-layout.json").write_text("Synthetic layout; never replayed.\n")
            for name in parts:
                (snapshot / name).write_bytes(b"synthetic part bytes")
        manifest = {p.relative_to(snapshot).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in snapshot.rglob("*") if p.is_file()}
        (snapshot / "manifest.json").write_text(json.dumps(manifest))
        self.git("add", ".")
        self.git("-c", "user.name=Roster fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--quiet", "-m", "Authored synthetic download roster")
        return self.git("rev-parse", "HEAD")

    def test_actual_immutable_v25_has_all_nine_snapshot_files_and_two_original_helpers(self):
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        snapshot = self.relative / "snapshots/20261113-v25"
        paths = published_paths(ROOT, commit, snapshot)
        self.assertEqual(len(paths), 11)
        self.assertIn(snapshot / "evidence.tar.gz", paths)
        self.assertNotIn(self.relative / "snapshot_control_archives.py", paths)

    def test_pinned_schema_two_gets_every_part_and_both_new_helpers_after_working_tree_deletion(self):
        parts = ("evidence-part-0001.tar.gz", "evidence-part-0002.tar.gz", "evidence-part-0003.tar.gz")
        commit = self.commit(2, parts)
        shutil.rmtree(self.root / self.snapshot)
        paths = published_paths(self.root, commit, self.snapshot)
        self.assertEqual(len(paths), 16)
        self.assertTrue({self.snapshot / name for name in parts} <= set(paths))
        self.assertIn(self.relative / "snapshot_archives.py", paths)
        self.assertIn(self.relative / "snapshot_control_archives.py", paths)

    def test_older_pinned_v1_roster_is_independent_of_current_v2_tree(self):
        old = self.commit(1)
        self.commit(2, ("evidence-part-0001.tar.gz", "evidence-part-0002.tar.gz"))
        paths = published_paths(self.root, old, self.snapshot)
        self.assertEqual(len(paths), 11)
        self.assertIn(self.snapshot / "evidence.tar.gz", paths)
        self.assertFalse(any(p.name.startswith("evidence-part-") for p in paths))

    def test_boolean_storage_schema_is_refused_before_downloading(self):
        commit = self.commit(True, ("evidence-part-0001.tar.gz",))
        with self.assertRaisesRegex(AssertionError, "Unsupported published storage schema"):
            published_paths(self.root, commit, self.snapshot)

    def test_committed_missing_part_is_refused_even_when_remaining_files_are_present(self):
        self.commit(2, ("evidence-part-0001.tar.gz", "evidence-part-0002.tar.gz"))
        self.git("rm", "--quiet", str(self.snapshot / "evidence-part-0002.tar.gz"))
        self.git("-c", "user.name=Roster fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--quiet", "-m", "Synthetic incomplete archive roster")
        with self.assertRaisesRegex(AssertionError, "Complete committed snapshot inventory required"):
            published_paths(self.root, self.git("rev-parse", "HEAD"), self.snapshot)

    def test_all_old_controls_remain_and_both_new_groups_add_sixteen_refusals(self):
        targets = json.loads((ROOT / self.relative / "snapshots/20261113-v25/targets.json").read_text())
        self.assertEqual(expected_counts(targets), (6, 65))
        targets.update(ptx_batched_proof={}, ptx_linear_proof={})
        self.assertEqual(expected_counts(targets), (8, 81))
        targets.update(ptx_rotary_proof={})
        self.assertEqual(expected_counts(targets), (9, 89))


if __name__ == "__main__":
    unittest.main()
