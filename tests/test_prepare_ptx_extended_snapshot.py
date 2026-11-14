"""Retain actual earlier evidence and render the recorded five-kernel scope."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

from reproduction.paper_results.prepare_ptx_extended_snapshot import (
    BASELINE, ROOT, augment_auditor, check_retained_evidence, prepare_snapshot,
)


def read(path):
    return json.loads(path.read_text())


class ExtendedPtxSnapshotPreparationTests(unittest.TestCase):
    def test_every_original_evidence_file_and_both_definitions_are_byte_identical(self):
        config = read(ROOT / BASELINE / "targets.json")
        retained = check_retained_evidence(config)
        self.assertEqual(len(retained), 3623)
        self.assertIn("reproduction/paper_results/ptx_matrix_evidence.py", retained)

    def test_old_member_cannot_be_removed_from_all_declared_groups(self):
        config = read(ROOT / BASELINE / "targets.json")
        removed = "reproduction/paper_results/ptx_matrix_evidence.py"
        config["evidence_groups"] = {key: [n for n in names if n != removed]
                                     for key, names in config["evidence_groups"].items()}
        with self.assertRaisesRegex(ValueError, "Every earlier evidence member must remain declared"):
            check_retained_evidence(config)

    def test_augmented_frozen_renderer_distinguishes_kernels_checks_and_failed_attempts(self):
        source = (ROOT / BASELINE / "auditor.py").read_text()
        namespace = {"__name__": "authored_five_kernel_ledger_renderer",
                     "__file__": str(ROOT / "reproduction/paper_results/audit.py")}
        exec(compile(augment_auditor(source), "authored-five-kernel-ledger.py", "exec"), namespace)
        report = copy.deepcopy(read(ROOT / BASELINE / "results/audit.json"))
        records = read(ROOT / "reproduction/paper_results/snapshot-v26-ptx-reader-validation-v1/standalone-reader-results.json")
        for kind, key in (("bmm", "ptx_batched_evidence_checks"), ("linear", "ptx_linear_evidence_checks")):
            report[key] = records[kind]
            path = "reproduction/ptx/results/full-size-" + kind + "-proof-v1/RESULTS.md"
            report["evidence_links"][path] = "https://github.com/harsh-nod/lark/blob/" + "0" * 40 + "/" + path
        rendered = namespace["render"](report, ROOT).decode()
        for expected in ("five independent full-size PTX development kernels", "all 138 instructions",
                         "All 179 instructions", "bias added before", "One failed official export",
                         "twelve earlier development attempts, including five failures",
                         "The original paper is not fully reproduced"):
            self.assertIn(expected.lower(), rendered.lower())
        self.assertIs(report["original_paper_fully_reproduced"], False)
        self.assertIsNone(report["completion_percentage"])

    def test_already_augmented_or_unexpected_frozen_source_is_refused(self):
        once = augment_auditor((ROOT / BASELINE / "auditor.py").read_text())
        with self.assertRaisesRegex(ValueError, "Frozen v25 auditor integration point differs"):
            augment_auditor(once)

    def test_missing_actual_receipts_are_refused_before_any_snapshot_is_created(self):
        with tempfile.TemporaryDirectory(prefix="lark-five-proof-preflight-") as temporary:
            root = Path(temporary)
            snapshot = root / "must-not-be-created"
            with self.assertRaisesRegex(ValueError, "Complete BMM/Linear publication, source CI, main"):
                prepare_snapshot(evidence_commit="0" * 40, source_archive=root / "must-not-be-read",
                                 snapshot=snapshot, root=root)
            self.assertFalse(snapshot.exists())


if __name__ == "__main__":
    unittest.main()
