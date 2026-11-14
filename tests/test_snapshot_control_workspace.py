"""Bound temporary storage after verification while preserving failures and inputs."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import shutil
import tempfile
import unittest

from reproduction.paper_results.check_snapshot_controls import control_workspace, release_completed_control


class ControlWorkspaceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-control-workspace-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.input = self.root / "immutable-input"
        self.input.mkdir()
        self.payload = bytes(range(256)) * 4096
        (self.input / "complete-payload.bin").write_bytes(self.payload)
        self.log = self.root / "verified.log"

    def test_complete_copied_payload_remains_until_the_expected_outcome_is_verified(self):
        with control_workspace(self.root) as root:
            copied = root / "complete-control"
            shutil.copytree(self.input, copied)
            self.assertEqual((copied / "complete-payload.bin").read_bytes(), self.payload)
            with self.assertRaisesRegex(ValueError, "must be verified"):
                release_completed_control(copied, root)
            self.assertEqual((copied / "complete-payload.bin").read_bytes(), self.payload)
            self.log.write_text("Expected gate verified after reading the complete copied payload.\n")
            release_completed_control(copied, root, expected_outcome_verified=True)
            self.assertFalse(copied.exists())
            self.assertTrue(self.log.is_file())
            self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)

    def test_an_unexpected_failure_keeps_its_complete_copied_input_and_log(self):
        with self.assertRaisesRegex(RuntimeError, "unexpected gate"):
            with control_workspace(self.root) as root:
                copied = root / "failed-control"
                shutil.copytree(self.input, copied)
                self.log.write_text("Unexpected replay outcome; retained for inspection.\n")
                raise RuntimeError("unexpected gate")
        self.assertEqual((copied / "complete-payload.bin").read_bytes(), self.payload)
        self.assertTrue(self.log.is_file())
        self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)

    def test_successful_workspace_cleanup_leaves_the_input_and_all_logs(self):
        with control_workspace(self.root) as root:
            copied = root / "checked-control"
            shutil.copytree(self.input, copied)
            self.assertEqual((copied / "complete-payload.bin").read_bytes(), self.payload)
            self.log.write_text("Completed full-copy check.\n")
            release_completed_control(copied, root, expected_outcome_verified=True)
        self.assertFalse(root.exists())
        self.assertTrue(self.log.is_file())
        self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)

    def test_original_input_outside_the_workspace_cannot_be_released(self):
        with control_workspace(self.root) as root:
            with self.assertRaisesRegex(ValueError, "Only a direct copied control"):
                release_completed_control(self.input, root, expected_outcome_verified=True)
            self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)

    def test_positive_baseline_is_not_a_direct_false_control_copy(self):
        with control_workspace(self.root) as root:
            positive = root / "isolated/snapshot"
            positive.parent.mkdir()
            shutil.copytree(self.input, positive)
            with self.assertRaisesRegex(ValueError, "Only a direct copied control"):
                release_completed_control(positive, root, expected_outcome_verified=True)
            self.assertEqual((positive / "complete-payload.bin").read_bytes(), self.payload)

    def test_a_symlink_cannot_release_its_original_target(self):
        with control_workspace(self.root) as root:
            alias = root / "symlink-control"
            alias.symlink_to(self.input, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "Only a direct copied control"):
                release_completed_control(alias, root, expected_outcome_verified=True)
            self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)

    def test_two_workers_each_verify_the_full_copy_before_releasing_only_their_own(self):
        with control_workspace(self.root) as root:
            def check(index):
                copied = root / str(index)
                shutil.copytree(self.input, copied)
                self.assertEqual((copied / "complete-payload.bin").read_bytes(), self.payload)
                log = self.root / (str(index) + ".log")
                log.write_text("Complete payload verified.\n")
                release_completed_control(copied, root, expected_outcome_verified=True)
                return copied, log

            with ThreadPoolExecutor(max_workers=2) as pool:
                outputs = list(pool.map(check, range(2)))
            self.assertTrue(all(not copied.exists() and log.is_file() for copied, log in outputs))
            self.assertEqual((self.input / "complete-payload.bin").read_bytes(), self.payload)


if __name__ == "__main__":
    unittest.main()
