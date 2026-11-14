"""Early FFN consistency guards never replace the complete frozen audit."""

import copy
import hashlib
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from reproduction.paper_results import ptx_ffn_release as release
from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results.check_snapshot_controls import FFN_CONTROLS, mutate_ffn_evidence
from reproduction.paper_results.ptx_ffn_evidence import Recording

ROOT = Path(__file__).resolve().parents[1]


class FfnPreflightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.protocol = release.load_protocol()
        cls.config = {"ptx_ffn_proof": {k: cls.protocol[k] for k in release.SPEC_KEYS}}
        cls.originals = {n: (ROOT / n).read_bytes() for n in cls.protocol["retained_files"]}

    def test_publication_preflight_uses_only_metadata_and_accepts_actual_records(self):
        published = set(self.protocol["publication_files"])

        class Metadata(Recording):
            def content(self, name):
                if name in published:
                    raise AssertionError("The full auditor must separately check actual published bytes")
                return super().content(name)

        self.assertIsNone(replay.preflight_ffn_publication(Metadata(ROOT), self.protocol))

    def test_actual_ci_checker_is_invoked_fresh_on_each_preflight(self):
        script = ROOT / "reproduction/paper_results/audit.py"
        with patch.dict(sys.modules, {"ptx_ffn_release": release}):
            with patch.object(replay, "read", return_value=self.config):
                with patch.object(release, "check_ci", wraps=release.check_ci) as checker:
                    replay.preflight_frozen_ffn(script)
                    replay.preflight_frozen_ffn(script)
        self.assertEqual(checker.call_count, 2)

    def test_real_coherent_header_forgeries_reach_the_same_frozen_refusal(self):
        for name, gate in FFN_CONTROLS:
            if name == "ffn-earlier-cancelled-CI-relabeled":
                continue  # Full history-byte checks remain in the complete auditor.
            with self.subTest(name=name):
                entries = self.originals.copy()
                mutate_ffn_evidence(entries, copy.deepcopy(self.config), name)

                class Overlay(Recording):
                    def content(self, path):
                        return entries[path] if path in entries else super().content(path)

                reader = Overlay(ROOT)
                with self.assertRaisesRegex(ValueError, "PTX ffn " + gate):
                    release.check_ci(reader, self.protocol)
                    replay.preflight_ffn_publication(reader, self.protocol)

    def test_ambient_ffn_reader_origin_cannot_replace_the_frozen_reader(self):
        script = ROOT / "reproduction/paper_results/audit.py"
        wrong = SimpleNamespace(__file__="/unrelated/ptx_ffn_release.py")
        with patch.dict(sys.modules, {"ptx_ffn_release": wrong}):
            with patch.object(replay, "read", return_value=self.config):
                with self.assertRaisesRegex(ValueError, "Frozen FFN reader origin differs"):
                    replay.preflight_frozen_ffn(script)

    def test_valid_preflight_always_runs_the_full_verified_auditor_again(self):
        with tempfile.TemporaryDirectory(prefix="lark-preflight-audit-order-") as temporary:
            script = Path(temporary) / "authored-auditor.py"
            script.write_text("# Authored call-order fixture; never interpreted as an experiment.\n")
            expected = hashlib.sha256(script.read_bytes()).hexdigest()
            events, original_argv, original_path = [], sys.argv[:], sys.path[:]
            original_tar_open = replay.tarfile.open
            try:
                with patch.object(replay, "preflight_frozen_release_headers", side_effect=lambda _: events.append("headers")):
                    with patch.object(replay.runpy, "run_path", side_effect=lambda *a, **k: events.append("complete-audit")):
                        replay.run_frozen_auditor(script, expected, [])
                        replay.run_frozen_auditor(script, expected, [])
            finally:
                replay.tarfile.open, sys.argv, sys.path = original_tar_open, original_argv, original_path
            self.assertEqual(events, ["headers", "complete-audit", "headers", "complete-audit"])


if __name__ == "__main__":
    unittest.main()
