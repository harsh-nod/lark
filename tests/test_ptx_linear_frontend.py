"""Keep the complete compiled Linear task and all new instruction data visible."""

import hashlib
import json
from pathlib import Path
import unittest

from lark_kernels import ptx_batched, ptx_matrix
from lark_kernels.ir import Refusal
from reproduction.ptx.linear_frontend import lean_instruction, prepare

CASE = Path(__file__).resolve().parents[1] / "reproduction/ptx/full-size/linear"


def inputs():
    return [(CASE / n).read_text() for n in ("kernel.ptx", "reference.py", "task.json")]


class PtxLinearFrontendTests(unittest.TestCase):
    def test_entire_original_source_task_and_real_backward_loop_are_retained(self):
        source, reference, contract = inputs()
        task, translation = prepare(source, reference, contract)
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                         "5ae52a2a03b700ffebe4de2d10c69e9fc3f34dea2d99e1bd3ad1c2472ef6e273")
        self.assertEqual(translation.readback(), source)
        self.assertEqual(len(translation.instructions), 179)
        self.assertEqual(len(translation.registers), 189)
        self.assertEqual(translation.labels, {"$L__BB0_1": 50})
        self.assertEqual(translation.instructions[43], ["signExtend32", 18, 11])
        self.assertEqual(translation.instructions[167], ["branch", 1, 50])
        self.assertEqual(translation.instructions[169], ["shiftLeft64", 48, 18, 1])
        self.assertEqual(translation.instructions[-1], ["ret"])
        self.assertEqual([b.shape for b in task.buffers], [(64, 256), (256, 512), (512,), (64, 512)])
        self.assertEqual((task.grid, task.block, task.warp, task.fuel), (32768, 1, 32, (1030, 1, 1, 1)))

    def test_reduced_shape_fuel_or_boolean_counter_cannot_replace_the_fixed_task(self):
        source, reference, contract = inputs()
        for field, value in (("fuel", [1031, 1, 1, 1]), ("fuel", [1030, True, 1, 1]),
                             ("launch", {"grid": 32768, "block": True, "warp": 32}),
                             ("launch", {"grid": 32768, "block": 1, "warp": 64})):
            changed = json.loads(contract)
            changed[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(Refusal):
                prepare(source, reference, json.dumps(changed))
        changed = json.loads(contract)
        changed["buffers"][0]["shape"][0] = 32
        changed["buffers"][3]["shape"][0] = 32
        changed["launch"]["grid"] = 16384
        with self.assertRaises(Refusal):
            prepare(source, reference, json.dumps(changed))

    def test_reference_operator_cast_order_and_extra_statements_are_refused(self):
        source, reference, contract = inputs()
        for altered in (reference.replace(" + bias.float()", " * bias.float()"),
                        reference.replace("a.float() @ b.float() + bias.float()",
                                          "(a.float() @ b.float()).half() + bias"),
                        reference + "\nraise RuntimeError('reference must remain data')\n"):
            with self.subTest(reference=altered), self.assertRaises(Refusal):
                prepare(source, altered, contract)

    def test_new_constructors_refuse_injection_booleans_bad_registers_and_shift_counts(self):
        for instruction in (["signExtend32", True, 11], ["signExtend32", 18, 256],
                            ["shiftLeft64", 48, 18, True], ["shiftLeft64", 48, 18, -1],
                            ["shiftLeft64", 48, 18, 2**32], ["signExtend32\naxiom bad : False", 18, 11]):
            with self.subTest(instruction=instruction), self.assertRaises(Refusal):
                lean_instruction(instruction)

    def test_both_new_operations_and_changed_product_remain_in_the_emitted_program(self):
        source, reference, contract = inputs()
        first = prepare(source, reference, contract)[1]
        altered = prepare(source.replace("mul.rn.f32", "add.rn.f32", 1), reference, contract)[1]
        self.assertIn("(.signExtend32 18 11)", first.lean_program())
        self.assertIn("(.shiftLeft64 48 18 1)", first.lean_program())
        self.assertNotEqual(first.instructions, altered.instructions)
        self.assertNotEqual(first.lean_program(), altered.lean_program())

    def test_grammar_acceptance_does_not_issue_an_existing_GEMM_or_BMM_certificate(self):
        for profile in (ptx_matrix, ptx_batched):
            with self.subTest(profile=profile.PROFILE), self.assertRaises(Refusal):
                profile.prepare_certificate(*inputs())


if __name__ == "__main__":
    unittest.main()
