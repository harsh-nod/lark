import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from lark_kernels import certificate
from lark_kernels.ir import Refusal, Task
from lark_kernels.frontend import translate
from lark_kernels.proof_syntax import check_terms
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parents[1]
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class ProofPolicyTests(unittest.TestCase):
    def test_meta_execution_keywords_are_rejected_in_every_slot(self):
        for slot in certificate.DEFAULT_PROOFS:
            for command in ("run_meta", "run_elab", "run_cmd", "run_io", "run_tac"):
                proofs = dict(certificate.DEFAULT_PROOFS)
                proofs[slot] = "by rfl\n" + command + ' Lean.logInfo "UNREACHABLE"'
                with self.subTest(slot=slot, command=command), self.assertRaises(Refusal):
                    certificate.validate_proofs(proofs)


@unittest.skipUnless(LEAN, "Lean 4.19.0 is required")
class ProofTermParserTests(unittest.TestCase):
    def test_all_standard_slots_parse_without_elaborating_them(self):
        ok, log = check_terms(certificate.DEFAULT_PROOFS, LEAN, 180)
        self.assertTrue(ok, log)
        self.assertIn("LARK_PROOF_TERMS_OK 3", log)
        # Parsing does not establish the truth or type correctness of a proof.
        ok, log = check_terms({"x": "by exact nonexistent_constant"}, LEAN, 180)
        self.assertTrue(ok, log)

    def test_trailing_commands_are_rejected_without_execution(self):
        for command in (
            "open Nat",
            "export Nat (zero)",
            'local notation "hidden" => True',
            'run_meta Lean.logInfo "UNREACHABLE_PROOF_COMMAND"',
        ):
            with self.subTest(command=command):
                ok, log = check_terms({"x": "by rfl\n" + command}, LEAN, 180)
                self.assertFalse(ok, log)
                self.assertIn("Proof must be exactly one term", log)
                self.assertNotIn("UNREACHABLE_PROOF_COMMAND", [s.strip() for s in log.splitlines()])

    def test_sdk_refuses_a_command_before_candidate_elaboration(self):
        case = ROOT / "reproduction/cases/relu"
        task = Task.read(case / "task.json")
        tr = translate((case / "kernel.hip").read_text(), task)
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": dict(certificate.DEFAULT_PROOFS),
        }
        proposal["proofs"]["segmentation_data"] += "\nopen Nat"
        # This command deliberately passes lexical validation. The exact term
        # parser must provide the command boundary rather than a keyword list.
        certificate.validate_proofs(proposal["proofs"])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "proposal.json").write_text(json.dumps(proposal))
            with patch.object(
                certificate, "run_lean", side_effect=AssertionError("Candidate was elaborated")
            ):
                result = certificate.verify(
                    case / "kernel.hip",
                    case / "reference.py",
                    case / "task.json",
                    root / "certificate",
                    lean=LEAN,
                    timeout=180,
                    proposal_path=root / "proposal.json",
                )
            self.assertNotEqual(result["status"], "verified")
            self.assertIn(
                "expected end of input", (root / "certificate/proof-syntax-1.log").read_text()
            )

    def test_rehashed_certificate_cannot_add_a_top_level_command(self):
        case = ROOT / "reproduction/cases/relu"
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "certificate"
            result = certificate.verify(
                case / "kernel.hip",
                case / "reference.py",
                case / "task.json",
                target,
                lean=LEAN,
                timeout=180,
            )
            self.assertEqual(result["status"], "verified")
            certificate.check(target, lean=LEAN, timeout=180)
            task = Task.read(target / "task.json")
            tr = translate((target / "kernel.cu").read_text(), task)
            spec = read_spec((target / "reference.py").read_text(), task)
            proposal = json.loads((target / "proposal.json").read_text())
            proposal["proofs"]["segmentation_data"] += "\nopen Nat"
            (target / "proposal.json").write_text(json.dumps(proposal))
            (target / "Main.lean").write_text(certificate.render(task, tr, spec, proposal))
            report = json.loads((target / "report.json").read_text())
            report["files"] = {
                n: certificate.digest((target / n).read_bytes()) for n in report["files"]
            }
            (target / "report.json").write_text(json.dumps(report))
            with patch.object(
                certificate,
                "run_lean",
                side_effect=AssertionError("Rehashed candidate was elaborated"),
            ):
                with self.assertRaisesRegex(Refusal, "Proof must be exactly one term"):
                    certificate.check(target, lean=LEAN, timeout=180)
