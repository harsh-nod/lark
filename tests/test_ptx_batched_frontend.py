"""Preserve the real 32-batch task before any new formal profile is accepted."""

import hashlib
import json
from pathlib import Path
import unittest

from lark_kernels import ptx_matrix
from lark_kernels.ir import Refusal
from reproduction.ptx.batched_frontend import prepare

CASE = Path(__file__).resolve().parents[1] / "reproduction/ptx/full-size/bmm"


def inputs():
    return [(CASE / name).read_text() for name in ("kernel.ptx", "reference.py", "task.json")]


class PtxBatchedFrontendTests(unittest.TestCase):
    def test_all_original_batches_instructions_and_actual_backward_branch_are_retained(self):
        source, reference, contract = inputs()
        task, translation = prepare(source, reference, contract)
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                         "df13d4a76ce01ff72fb71eeeca866c5750885bb29d036c652ec9036c7c97cd81")
        self.assertEqual(translation.readback(), source)
        self.assertEqual(len(translation.instructions), 138)
        self.assertEqual(translation.labels, {"$L__BB0_1": 29})
        self.assertEqual(translation.instructions[131], ["branch", 1, 29])
        self.assertEqual(translation.instructions[-1], ["ret"])
        self.assertEqual([b.shape for b in task.buffers],
                         [(32, 64, 256), (32, 256, 512), (32, 64, 512)])
        self.assertEqual((task.grid, task.block, task.warp, task.fuel),
                         (1048576, 1, 32, (1030, 1, 1, 1)))

    def test_fewer_batches_cannot_replace_the_full_size_task(self):
        source, reference, contract = inputs()
        changed = json.loads(contract)
        for buffer in changed["buffers"]:
            buffer["shape"][0] = 2
        changed["launch"]["grid"] = 65536
        with self.assertRaises(Refusal):
            prepare(source, reference, json.dumps(changed))

    def test_wrong_launch_fuel_or_boolean_counter_is_refused(self):
        source, reference, contract = inputs()
        for field, value in (("fuel", [1031, 1, 1, 1]),
                             ("fuel", [1030, True, 1, 1]),
                             ("launch", {"grid": 1048576, "block": True, "warp": 32}),
                             ("launch", {"grid": 1048576, "block": 2, "warp": 32})):
            changed = json.loads(contract)
            changed[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(Refusal):
                prepare(source, reference, json.dumps(changed))

    def test_wrong_operator_argument_or_extra_reference_statement_is_refused(self):
        source, reference, contract = inputs()
        for changed in (reference.replace(" @ ", " + "),
                        reference.replace("b.float()", "a.float()"),
                        reference + "\nraise RuntimeError('must never execute reference')\n"):
            with self.subTest(reference=changed), self.assertRaises(Refusal):
                prepare(source, changed, contract)

    def test_modified_product_changes_the_complete_lean_program(self):
        source, reference, contract = inputs()
        first = prepare(source, reference, contract)[1]
        changed = prepare(source.replace("mul.rn.f32", "add.rn.f32", 1), reference, contract)[1]
        self.assertNotEqual(first.instructions, changed.instructions)
        self.assertNotEqual(first.lean_program(), changed.lean_program())

    def test_grammar_acceptance_cannot_issue_a_fixed_GEMM_certificate(self):
        with self.assertRaisesRegex(Refusal, "ptx-matrix-contract"):
            ptx_matrix.prepare_certificate(*inputs())


if __name__ == "__main__":
    unittest.main()
