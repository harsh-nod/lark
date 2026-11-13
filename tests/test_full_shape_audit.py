import contextlib
import io
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile
import unittest

from reproduction.local_models import audit_full_shape as audit

ROOT = Path(__file__).resolve().parents[1]


def extract(archive, destination):
    with tarfile.open(archive) as bundle:
        for member in bundle:
            name = PurePosixPath(member.name)
            if not member.isfile() or name.is_absolute() or ".." in name.parts:
                raise ValueError("Unsafe fixture member")
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(bundle.extractfile(member).read())


class FullShapeAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixtures = tempfile.TemporaryDirectory()
        cls.fixture_root = Path(cls.fixtures.name)
        cls.prepared = cls.fixture_root / "prepared"
        cls.pilot = cls.fixture_root / "pilot"
        base = ROOT / "reproduction/local_models/results"
        extract(base / "full-shape-preparation-v2/preparation.tar.gz", cls.prepared)
        extract(base / "full-shape-pilot-glm53-v1/pilot.tar.gz", cls.pilot)

    @classmethod
    def tearDownClass(cls):
        cls.fixtures.cleanup()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.recording = self.root / "recording"
        shutil.copytree(self.pilot, self.recording)
        self.case_path = self.recording / "cases/relu/results.json"
        self.report_path = self.recording / "results.json"

    def check(self, **kwargs):
        with contextlib.redirect_stdout(io.StringIO()):
            return audit.audit(self.recording, self.prepared, self.root / "audit", **kwargs)

    def change_case(self, function):
        case = audit.read(self.case_path)
        function(case)
        audit.run.write(self.case_path, case)
        report = audit.read(self.report_path)
        report["cases"][0] = case
        audit.run.write(self.report_path, report)

    def test_published_pilot_replays_all_requests_without_model_calls(self):
        result = self.check()
        self.assertEqual(len(result["bound_model_requests"]), 4)
        self.assertEqual(result["recorded_verified_model_proofs"], 1)
        self.assertEqual(result["freshly_verified_model_proofs"], 0)
        self.assertEqual(result["model_calls_by_audit"], 0)
        self.assertFalse(result["complete_17_case_cohort"])
        self.assertEqual(result["reported_usage"]["total_tokens"], 37567)

    def test_pilot_cannot_satisfy_full_cohort_requirement(self):
        with self.assertRaisesRegex(ValueError, "seventeen"):
            self.check(require_full=True)

    def test_test_stub_cannot_be_relabelled_as_real_inference(self):
        report = audit.read(self.report_path)
        report["test_stub"] = True
        audit.run.write(self.report_path, report)
        with self.assertRaisesRegex(ValueError, "stub"):
            self.check()

    def test_frontend_label_cannot_override_frozen_hip_preparation(self):
        report = audit.read(self.report_path)
        report["source_language"] = "cuda"
        audit.run.write(self.report_path, report)
        with self.assertRaisesRegex(ValueError, "scope"):
            self.check()

    def test_legacy_hip_controller_cannot_claim_cuda_preparation(self):
        prepared = self.root / "cuda-prepared"
        extract(ROOT / "reproduction/local_models/results/full-shape-cuda-preparation-v1/preparation.tar.gz",
                prepared)
        with self.assertRaisesRegex(ValueError, "does not support"):
            audit.audit(self.recording, prepared, self.root / "audit")

    def test_false_proof_and_usage_counts_are_refused(self):
        for key in ("verified_model_proofs", "model_inference_calls", "request_attempts"):
            with self.subTest(key=key):
                report = audit.read(self.report_path)
                report[key] += 1
                audit.run.write(self.report_path, report)
                with self.assertRaises(ValueError):
                    self.check()
                shutil.rmtree(self.root / "audit", ignore_errors=True)
                shutil.copyfile(self.pilot / "results.json", self.report_path)

    def test_rehashed_changed_model_prompt_is_refused(self):
        folder = self.recording / "cases/relu/call-01/model"
        request = audit.read(folder / "request.json")
        request["messages"][1]["content"] += "\nAn extra model-visible hint."
        audit.run.write(folder / "request.json", request)
        receipt = audit.read(folder / "receipt.json")
        receipt["request_sha256"] = audit.run.sha(folder / "request.json")
        audit.run.write(folder / "receipt.json", receipt)
        with self.assertRaises(ValueError):
            self.check()

    def test_rehashed_raw_response_cannot_change_checked_proof(self):
        folder = self.recording / "cases/relu/call-04/model"
        response = audit.read(folder / "response.json")
        action = json.loads(response["choices"][0]["message"]["content"])
        action["proofs"]["segmentation_data"] += " "
        response["choices"][0]["message"]["content"] = json.dumps(action)
        audit.run.write(folder / "response.json", response)
        receipt = audit.read(folder / "receipt.json")
        receipt["response_sha256"] = audit.run.sha(folder / "response.json")
        audit.run.write(folder / "receipt.json", receipt)
        with self.assertRaises(ValueError):
            self.check()

    def test_protocol_refusal_cannot_be_relabelled_as_transport_failure(self):
        folder = self.recording / "cases/relu/call-01/model"
        request = audit.read(folder / "request.json")
        request["messages"][1]["content"] += "\nExtra unprovided hint"
        audit.run.write(folder / "request.json", request)
        receipt = audit.read(folder / "receipt.json")
        receipt["request_sha256"] = audit.run.sha(folder / "request.json")
        audit.run.write(folder / "receipt.json", receipt)
        for number in (2, 3, 4):
            shutil.rmtree(self.recording / f"cases/relu/call-{number:02d}")
        case = audit.read(self.case_path)
        case.update(status="runtime-uncertain", calls=case["calls"][:1],
                    proof_checks=0, library_reads=0, syntax_checks=0)
        case["calls"][0].update(status="runtime-or-context-error",
                                error="Model prompt or parameters differ")
        audit.run.write(self.case_path, case)
        report = audit.read(self.report_path)
        report.update(status="runtime-uncertain", cases=[case],
                      model_inference_calls=1, verified_model_proofs=0)
        report.update(audit.run.usage(self.recording))
        audit.run.write(self.report_path, report)
        with self.assertRaisesRegex(ValueError, "Recording protocol refused"):
            self.check()

    def test_rehashed_checked_main_cannot_change_fixed_task(self):
        folder = self.recording / "cases/relu/call-04"
        for name in ("proof-check", "independent-recheck"):
            path = folder / name / "Main.lean"
            path.write_text(path.read_text() + "\nexample : True := by trivial\n")
        digest = audit.run.sha(folder / "proof-check/Main.lean")
        self.change_case(lambda case: case["calls"][-1].update(main_sha256=digest))
        with self.assertRaises(ValueError):
            self.check()

    def test_rehashed_forbidden_axiom_log_is_refused(self):
        folder = self.recording / "cases/relu/call-04"
        for name in ("proof-check", "independent-recheck"):
            path = folder / name / "lean.log"
            text = path.read_text().replace("propext", "Injected.forbiddenAxiom")
            self.assertNotEqual(text, path.read_text())
            path.write_text(text)
        self.change_case(lambda case: case["calls"][-1].update(
            lean_log_sha256=audit.run.sha(folder / "proof-check/lean.log"),
            recheck_log_sha256=audit.run.sha(folder / "independent-recheck/lean.log")))
        with self.assertRaises(ValueError):
            self.check()

    def test_changed_library_read_receipt_is_refused(self):
        path = self.recording / "cases/relu/call-01/library-read.json"
        value = audit.read(path)
        value["text"] += "\nUnprovided hint"
        audit.run.write(path, value)
        with self.assertRaisesRegex(ValueError, "library excerpt"):
            self.check()


if __name__ == "__main__":
    unittest.main()
