"""Real FFN records must reject coherent CI, publication and history forgeries."""

import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from reproduction.paper_results.check_snapshot_controls import FFN_CONTROLS, mutate_ffn_evidence
from reproduction.paper_results.ptx_ffn_evidence import Recording, sha
from reproduction.paper_results import ptx_ffn_release as release

ROOT = Path(__file__).resolve().parents[1]


class FfnReleaseEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.protocol = release.load_protocol()
        cls.originals = {n: (ROOT / n).read_bytes() for n in cls.protocol["retained_files"]}
        cls.config = {"ptx_ffn_proof": {k: cls.protocol[k] for k in release.SPEC_KEYS},
                      "current_runtime_sources": {}, "evidence_groups": {"ffn": [
                          *cls.protocol["retained_files"], *cls.protocol["matched_SDK_files"],
                          *[p.relative_to(ROOT).as_posix() for p in (ROOT / cls.protocol["prefix"]).iterdir()
                            if p.is_file()],
                      ]}}

    def test_actual_complete_family_has_one_pipeline_and_no_new_experiments(self):
        result = release.check_ptx_ffn_evidence(self.config)
        self.assertEqual(result["successful_source_CI_jobs"], 24)
        self.assertEqual(result["anonymous_publication_files"], 34)
        self.assertEqual(result["archive_members_checked"], 4416)
        self.assertEqual(result["recorded_source_CI_positive_builds"], 2)
        self.assertEqual(result["recorded_source_CI_commit"], self.protocol["published_source"])
        self.assertEqual(len(result["distinct_recorded_pipeline_identities"]), 1)
        self.assertEqual(len(result["independent_false_recording_refusals"]), 31)
        self.assertIs(result["captured_code_executed"], False)
        self.assertIs(result["original_paper_fully_reproduced"], False)
        self.assertEqual(result["fresh_Lean_checks"], 0)

    def test_complete_rehashed_forgeries_reach_their_expected_semantic_gates(self):
        for name, gate in FFN_CONTROLS:
            with self.subTest(name=name):
                entries = self.originals.copy()
                config = copy.deepcopy(self.config)
                mutate_ffn_evidence(entries, config, name)
                # Every changed file keeps its enclosing hash bindings coherent.
                # Older as-of-progress inventories are retained verbatim; they
                # are historical data, not fresh manifests of later files.
                for path, data in entries.items():
                    if path.endswith("/manifest.json"):
                        value = json.loads(data)
                        if type(value) is dict and all(type(v) is str for v in value.values()):
                            prefix = path.removesuffix("manifest.json")
                            for member, digest in value.items():
                                if (prefix + member in entries
                                        and entries[prefix + member] != self.originals[prefix + member]):
                                    self.assertEqual(sha(entries[prefix + member]), digest)

                class Overlay(Recording):
                    def content(self, path):
                        return entries[path] if path in entries else super().content(path)

                with patch.object(release, "Recording", Overlay):
                    with self.assertRaisesRegex(ValueError, "PTX ffn " + gate):
                        release.check_ptx_ffn_evidence(config)


if __name__ == "__main__":
    unittest.main()
