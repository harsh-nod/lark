import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

from reproduction.local_models import compare_full_shape as comparison

PACKET = Path(__file__).resolve().parents[1] / (
    "reproduction/local_models/results/full-shape-cohort-deepseek-v1"
)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def refresh(root):
    manifest = comparison.read(root / "manifest.json")
    write(root / "manifest.json", {n: comparison.run.sha(root / n) for n in manifest})


def rewrite_archive(root, archive, inventory, change):
    with tarfile.open(root / archive, "r:gz") as stream:
        files = {m.name: stream.extractfile(m).read() for m in stream.getmembers()}
    change(files)
    with tarfile.open(root / archive, "w:gz") as stream:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size = len(data)
            stream.addfile(info, io.BytesIO(data))
    write(root / inventory, {n: hashlib.sha256(b).hexdigest() for n, b in sorted(files.items())})
    refresh(root)


class FullShapeComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = comparison.compare([PACKET], allow_partial=True)

    def test_paper_success_only_cost_definition_on_real_complete_evidence(self):
        row = self.report["inputs"][0]
        first, second = (row["levels"][level] for level in ("level1", "level2"))
        self.assertEqual((first["tasks"], first["verified_within_budget"]), (12, 11))
        self.assertEqual((second["tasks"], second["verified_within_budget"]), (5, 5))
        self.assertEqual(first["mean_denominator_verified_tasks"], 11)
        self.assertEqual(first["successful_task_reported_usage"],
                         {"prompt_tokens": 1570901, "completion_tokens": 233561,
                          "total_tokens": 1804462})
        self.assertAlmostEqual(first["mean_over_verified_tasks_tokens"]["prompt_tokens"],
                               142809.18181818182)
        self.assertEqual(second["mean_over_verified_tasks_tokens"]["completion_tokens"], 44669)
        self.assertEqual(row["cohort_reported_usage"]["total_tokens"], 3844318)
        self.assertEqual(row["recorded_counts"]["first_response_verified"], 0)
        self.assertEqual(row["recorded_counts"]["first_actual_lean_check_verified"], 14)
        self.assertEqual(row["recorded_counts"]["additional_fresh_kernel_checks"], 32)
        self.assertFalse(self.report["original_paper_fully_reproduced"])

    def test_partial_roster_is_explicit_and_duplicate_cohorts_refused(self):
        self.assertEqual(len(self.report["missing_cohorts"]), 5)
        self.assertFalse(self.report["all_six_independent_cohorts_present"])
        with self.assertRaisesRegex(ValueError, "Missing independent cohorts"):
            comparison.compare([PACKET])
        with self.assertRaisesRegex(ValueError, "Duplicate model/language"):
            comparison.compare([PACKET, PACKET], allow_partial=True)

    def test_fully_rehashed_false_scope_and_language_are_refused(self):
        controls = (("original_paper_fully_reproduced", True, "completion overclaim"),
                    ("test_stub", True, "non-stub"),
                    ("source_language", "cuda", "Preparation/source language"))
        for field, value, error in controls:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / "packet"
                shutil.copytree(PACKET, root)
                report = comparison.read(root / "results.json")
                report[field] = value
                write(root / "results.json", report)
                refresh(root)
                with self.assertRaisesRegex(ValueError, error):
                    comparison.load_packet(root)

    def test_rehashed_top_level_success_count_cannot_override_raw_calls(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "packet"
            shutil.copytree(PACKET, root)
            report = comparison.read(root / "results.json")
            report["counts"]["verified_within_budget"] = 17
            write(root / "results.json", report)
            refresh(root)
            with self.assertRaisesRegex(ValueError, "Cohort totals/usage"):
                comparison.load_packet(root)

    def test_rehashed_binding_cannot_substitute_the_preparation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "packet"
            shutil.copytree(PACKET, root)
            binding = comparison.read(root / "binding.json")
            binding["preparation_archive_sha256"] = "0" * 64
            write(root / "binding.json", binding)
            refresh(root)
            with self.assertRaisesRegex(ValueError, "Pinned preparation archive"):
                comparison.load_packet(root)

    def test_rehashed_response_and_receipt_usage_recomputes_case_cost(self):
        def change(files):
            prefix = "cases/relu/call-01/model/"
            response = json.loads(files[prefix + "response.json"])
            response["usage"]["completion_tokens"] += 1
            response["usage"]["total_tokens"] += 1
            files[prefix + "response.json"] = (json.dumps(response, indent=2) + "\n").encode()
            receipt = json.loads(files[prefix + "receipt.json"])
            receipt["usage"] = response["usage"]
            receipt["response_sha256"] = comparison.digest(files[prefix + "response.json"])
            files[prefix + "receipt.json"] = (json.dumps(receipt, indent=2) + "\n").encode()

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "packet"
            shutil.copytree(PACKET, root)
            rewrite_archive(root, "cohort.tar.gz", "cohort-files.json", change)
            with self.assertRaisesRegex(ValueError, "Per-case summary"):
                comparison.load_packet(root)

    def test_rehashed_fresh_main_still_must_match_accepted_raw_main(self):
        def change(files):
            files["protocol-replay/relu/call-05/fresh-kernel-1/Main.lean"] += b"\n-- changed\n"

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "packet"
            shutil.copytree(PACKET, root)
            rewrite_archive(root, "audit.tar.gz", "audit-files.json", change)
            with self.assertRaisesRegex(ValueError, "Fresh accepted Main/log"):
                comparison.load_packet(root)

    def test_no_verified_tasks_has_undefined_success_mean_and_nonzero_total(self):
        row = copy.deepcopy(self.report["inputs"][0]["cases"][-1])
        row.update(status="budget-exhausted", first_response_verified=False,
                   first_actual_lean_check_verified=False)
        stats = comparison.level_stats([row])
        self.assertEqual(stats["mean_denominator_verified_tasks"], 0)
        self.assertEqual(stats["mean_over_verified_tasks_tokens"],
                         {"prompt_tokens": None, "completion_tokens": None, "total_tokens": None})
        self.assertGreater(stats["all_task_reported_usage"]["total_tokens"], 0)


if __name__ == "__main__":
    unittest.main()
