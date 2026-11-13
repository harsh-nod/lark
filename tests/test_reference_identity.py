from pathlib import Path
import unittest

from reproduction.local_models import reference_identity as study


class ReferenceIdentityAuditTests(unittest.TestCase):
    def setUp(self):
        self.log = (Path(__file__).parent / "fixtures/reference-identity-pilot.log").read_text()

    def test_real_pilot_checks_both_source_proofs_and_the_identity(self):
        self.assertTrue(study.log_audits(self.log))
        self.assertEqual(len(study.TAGS), 13)

    def test_missing_and_duplicate_declaration_audits_are_refused(self):
        for line in self.log.splitlines():
            with self.subTest(line=line):
                self.assertFalse(study.log_audits(self.log.replace(line + "\n", "")))
                self.assertFalse(study.log_audits(self.log + line + "\n"))

    def test_forged_identity_axiom_and_failed_compilation_are_refused(self):
        actual = "'hip_cuda_spec_eq' does not depend on any axioms"
        forged = "'hip_cuda_spec_eq' depends on axioms: [Injected.falseAxiom]"
        self.assertIn(actual, self.log)
        self.assertFalse(study.log_audits(self.log.replace(actual, forged)))
        self.assertFalse(study.log_audits(self.log + "Main.lean:1:0: error: failed\n"))
        self.assertFalse(study.log_audits(self.log + "declaration uses sorry\n"))

    def test_original_blocks_cannot_override_fixed_resource_limits(self):
        with self.assertRaisesRegex(ValueError, "option"):
            study.main_source("set_option maxHeartbeats 999999999", "")
        main = study.main_source("namespace LarkCertificate\nend LarkCertificate", "")
        self.assertEqual(main.count("set_option maxRecDepth 10000"), 1)
        self.assertEqual(main.count("set_option maxHeartbeats 2000000"), 1)

    def test_actual_wrong_operator_refusal_retains_the_resource_bound_diagnostic(self):
        root = Path(__file__).parent / "fixtures"
        main = (root / "reference-identity-wrong-operator.lean").read_text()
        log = (root / "reference-identity-wrong-operator.log").read_text()
        self.assertEqual(study.wrong_operator_refusal(main, log), "fixed-recursion-limit")
        self.assertFalse(study.log_audits(log))
        changed = log.replace("Main.lean:111:", "Main.lean:1:")
        self.assertNotEqual(changed, log)
        with self.assertRaisesRegex(ValueError, "outside"):
            study.wrong_operator_refusal(main, changed)


if __name__ == "__main__":
    unittest.main()
