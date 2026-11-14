"""The six-kernel renderer preserves the paper audit and distinguishes repeated checks."""

import copy
import json
from pathlib import Path
import unittest

from reproduction.paper_results.prepare_ptx_rotary_snapshot import (
    augment_auditor, check_retained_evidence, preservation_plan,
)
from reproduction.paper_results.ptx_rotary_evidence import PROTOCOLS


ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "reproduction/paper_results/snapshots/20261113-v26"


class RotaryAuditorPreparationTests(unittest.TestCase):
    def test_render_adds_one_kernel_and_keeps_original_results_incomplete(self):
        source = augment_auditor((BASELINE / "auditor.py").read_text())
        namespace = {"__name__": "authored_six_kernel_renderer_fixture",
                     "__file__": str(ROOT / "reproduction/paper_results/audit.py")}
        exec(compile(source, "owned-six-kernel-renderer.py", "exec"), namespace)
        report = copy.deepcopy(json.loads((BASELINE / "results/audit.json").read_text()))
        report["ptx_rotary_evidence_checks"] = {**PROTOCOLS["counters"],
                                               "scope": "Authored renderer fixture, not a release claim."}
        name = "reproduction/ptx/results/full-size-rotary-proof-v1/RESULTS.md"
        report["evidence_links"][name] = "https://github.com/harsh-nod/lark/blob/" + "0" * 40 + "/" + name
        result = namespace["render"](report, ROOT).decode()
        for text in ("six independent full-size PTX development", "All 51 instructions and 32768 lanes",
                     "4 retained Main checks and 3 rechecks", "17 earlier development attempts",
                     "11 failures", "independently defined", "The original paper is not fully reproduced"):
            self.assertIn(text, result)
        self.assertIs(report["original_paper_fully_reproduced"], False)
        self.assertIsNone(report["completion_percentage"])
        self.assertEqual(report["counts"], {"tables": 17, "outer_figure_groups": 7, "narrative_anchors": 16})

    def test_modified_or_already_augmented_auditors_are_refused(self):
        original = (BASELINE / "auditor.py").read_text()
        for source in (original + "\n", augment_auditor(original)):
            with self.assertRaisesRegex(ValueError, "Frozen v26 auditor integration point differs"):
                augment_auditor(source)

    def test_all3792_original_paths_and_hashes_survive_runtime_changes(self):
        config = json.loads((BASELINE / "targets.json").read_text())
        config["preserved_evidence_origins"] = preservation_plan()
        retained = check_retained_evidence(config)
        self.assertEqual(len(retained), 3792)
        for name in ("reproduction/paper_results/replay_snapshot.py",
                     "reproduction/paper_results/check_snapshot_controls.py",
                     "reproduction/paper_results/snapshot_control_archives.py",
                     "tests/test_snapshot_control_archives.py"):
            self.assertIn(name, config["preserved_evidence_origins"])
            self.assertEqual(config["preserved_evidence_origins"][name]["sha256"], retained[name])

    def test_old_evidence_member_cannot_be_removed_from_all_groups(self):
        config = json.loads((BASELINE / "targets.json").read_text())
        removed = "reproduction/paper_results/ptx_matrix_evidence.py"
        config["evidence_groups"] = {key: [n for n in names if n != removed]
                                     for key, names in config["evidence_groups"].items()}
        with self.assertRaisesRegex(ValueError, "Every earlier evidence member must remain declared"):
            check_retained_evidence(config)


if __name__ == "__main__":
    unittest.main()
