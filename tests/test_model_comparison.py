"""Corruption controls for recorded-data auditing; these tests make no model calls."""

from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from lark_kernels import certificate
from lark_kernels.frontend import translate
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec
from reproduction.local_models import compare_models as comparison

ROOT = Path(__file__).resolve().parents[1] / "reproduction/local_models/results"
SMALL = ROOT / "pilot-deepseek-budget4096-20261109/deepseek-budget4096-remote"
EXPANDED = ROOT / "pilot-deepseek-expanded-20261109/deepseek-budget4096-additional14-remote"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def load(path):
    return json.loads(path.read_text())


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ComparisonAuditTests(unittest.TestCase):
    def test_rehashed_weakened_request_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "run"
            shutil.copytree(SMALL, root)
            request_path = root / "case-00/attempt-01/request.json"
            request = load(request_path)
            body = json.loads(request["messages"][1]["content"])
            self.assertIn("flatten segments = program", body["lean_source"])
            body["lean_source"] = body["lean_source"].replace("flatten segments = program", "True")
            request["messages"][1]["content"] = json.dumps(body)
            write(request_path, request)
            receipt_path = request_path.with_name("receipt.json")
            receipt = load(receipt_path)
            receipt["request_sha256"] = digest(request_path)
            write(receipt_path, receipt)
            with self.assertRaisesRegex(comparison.AuditError, "immutable statements"):
                comparison.audit_run(root)

    def test_later_success_does_not_become_first_attempt_success(self):
        # Instrument the invocation only; the real certificate is separately
        # rechecked by the CLI integration and the test below.
        with patch.object(
            certificate, "check", return_value="unit-test invocation record"
        ) as checked:
            audited, logs = comparison.audit_run(EXPANDED, lean="/unit-test/lean")
        row = next(c for c in audited["cases"] if c["case"].endswith("/depthwise_conv"))
        self.assertFalse(row["first_verified"])
        self.assertTrue(row["verified_within_recorded_budget"])
        self.assertEqual(row["requests"], 3)
        self.assertEqual(set(logs), {"depthwise_conv"})
        checked.assert_called_once()

    def test_duplicate_cases_cannot_complete_a_cohort(self):
        with self.assertRaisesRegex(comparison.AuditError, "Duplicate cohort fixture"):
            comparison.audit_cohort("deepseek", [SMALL, SMALL], lean="/unused/lean")

    def test_missing_reasoning_usage_remains_explicit(self):
        for details in ("missing", "null"):
            with self.subTest(details=details), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "run"
                shutil.copytree(SMALL, root)
                base = root / "case-00/attempt-01"
                response = load(base / "response.json")
                if details == "missing":
                    del response["usage"]["completion_tokens_details"]
                else:
                    response["usage"]["completion_tokens_details"] = None
                write(base / "response.json", response)
                receipt = load(base / "receipt.json")
                receipt["usage"] = response["usage"]
                receipt["response_sha256"] = digest(base / "response.json")
                write(base / "receipt.json", receipt)
                audited, _ = comparison.audit_run(root)
                self.assertFalse(audited["all_attempt_usage"]["usage_incomplete"])
                self.assertTrue(audited["all_attempt_usage"]["reasoning_usage_incomplete"])

    def test_transport_failure_is_not_a_lean_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "run"
            shutil.copytree(SMALL, root)
            for name in ("case-01", "case-02", "case-00/attempt-02", "case-00/attempt-03"):
                shutil.rmtree(root / name)
            base = root / "case-00/attempt-01"
            for name in ("response.json", "Main.lean", "proposal.json", "lean.log"):
                (base / name).unlink(missing_ok=True)
            receipt = load(base / "receipt.json")
            receipt.pop("response_sha256")
            receipt.pop("finish_reason")
            receipt.update(status="error", usage=None, error="unit-test timeout")
            write(base / "receipt.json", receipt)
            case = load(root / "case-00/result.json")
            case.update(
                status="no-model-response",
                calls=[
                    {
                        "attempt": 1,
                        "status": "transport-or-response-error",
                        "error": "unit-test timeout",
                        "elapsed_seconds": 1.0,
                    }
                ],
            )
            write(root / "case-00/result.json", case)
            report = load(root / "results.json")
            report.update(
                cases=[case],
                attempts_per_case=1,
                request_attempts=1,
                inference_responses=0,
                usage_incomplete=True,
                reported_usage={"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0},
            )
            write(root / "results.json", report)
            audited, _ = comparison.audit_run(root)
            self.assertEqual(audited["lean_checks"], 0)
            self.assertEqual(audited["call_outcomes"], {"transport-or-response-error": 1})
            self.assertFalse(audited["cases"][0]["first_response_received"])
            self.assertTrue(audited["first_attempt_usage"]["usage_incomplete"])

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_valid_manual_proof_replacement_is_not_model_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "run"
            shutil.copytree(EXPANDED, root)
            cert = root / "case-02/certificate"
            proposal = deepcopy(load(cert / "proposal.json"))
            proposal["proofs"]["segmentation_data"] += "\n  "
            write(cert / "proposal.json", proposal)
            task = Task.read(cert / "task.json")
            tr = translate((cert / "kernel.cu").read_text(), task)
            spec = read_spec((cert / "reference.py").read_text(), task)
            (cert / "Main.lean").write_text(certificate.render(task, tr, spec, proposal))
            report = load(cert / "report.json")
            for name in ("proposal.json", "Main.lean"):
                report["files"][name] = digest(cert / name)
            write(cert / "report.json", report)
            # The edited proof is still mathematically valid and source-bound.
            # It must nevertheless be refused as evidence of model authorship.
            certificate.check(cert, lean=LEAN)
            with self.assertRaisesRegex(comparison.AuditError, "Exported tactics differ"):
                comparison.audit_run(root, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
