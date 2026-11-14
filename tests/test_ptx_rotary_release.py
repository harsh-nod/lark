"""Release claims require all actual jobs, typed counters and one exact source."""

import copy
from pathlib import Path
import unittest

from reproduction.paper_results.ptx_rotary_evidence import Recording
from reproduction.paper_results.ptx_rotary_release import check_source_ci


class RotarySourceCiGuardTests(unittest.TestCase):
    def setUp(self):
        self.reader = Recording(Path(__file__).parent, "rotary")
        # Authored protocol fixture; these records claim no actual CI execution.
        self.protocol = {"ci_jobs": ["synthetic-job-" + str(i) for i in range(24)],
                         "ci_run": 123, "published_source": "a" * 40,
                         "ci_branch": "synthetic-fixture"}
        self.summary = {"status": "exact-source-CI-all-24-passed", "source_commit": "a" * 40,
                        "run_id": 123, "original_paper_fully_reproduced": False,
                        "expected_jobs": list(self.protocol["ci_jobs"]), "successful_jobs": 24,
                        "model_calls": 0, "gpu_trials": 0, "CI_reruns": 0,
                        "new_registered_source_certificates": 0}
        self.run = {"id": 123, "head_sha": "a" * 40, "event": "push", "name": "Verify",
                    "head_branch": "synthetic-fixture", "status": "completed",
                    "conclusion": "success", "run_attempt": 1}
        self.jobs = {"total_count": 24, "jobs": [
            {"id": i, "name": name, "run_id": 123, "status": "completed", "conclusion": "success"}
            for i, name in enumerate(self.protocol["ci_jobs"], start=1)]}

    def check(self):
        check_source_ci(self.reader, self.summary, self.run, self.jobs, self.protocol)

    def test_complete_synthetic_protocol_is_consistent(self):
        self.check()

    def test_successful_summary_cannot_hide_one_pending_or_failed_job(self):
        for status, conclusion in (("queued", None), ("completed", "failure")):
            with self.subTest(status=status, conclusion=conclusion):
                self.jobs["jobs"][-1].update(status=status, conclusion=conclusion)
                with self.assertRaisesRegex(ValueError, "actual source CI differs"):
                    self.check()

    def test_different_source_rerun_or_duplicate_job_is_refused(self):
        original = copy.deepcopy((self.run, self.jobs))
        for mutation in (
            lambda: self.run.update(head_sha="b" * 40),
            lambda: self.run.update(run_attempt=2),
            lambda: self.jobs["jobs"][-1].update(id=1),
        ):
            self.run, self.jobs = copy.deepcopy(original)
            mutation()
            with self.assertRaisesRegex(ValueError, "actual source CI differs"):
                self.check()

    def test_boolean_and_float_counter_aliases_are_refused(self):
        for key, value in (("successful_jobs", 24.0), ("model_calls", False)):
            with self.subTest(key=key, value=value):
                old = self.summary[key]
                self.summary[key] = value
                with self.assertRaisesRegex(ValueError, "source CI execution counters differ"):
                    self.check()
                self.summary[key] = old
        self.run["run_attempt"] = True
        with self.assertRaisesRegex(ValueError, "actual source CI differs"):
            self.check()


if __name__ == "__main__":
    unittest.main()
