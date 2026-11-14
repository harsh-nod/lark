"""Full compiled RoPE reader and input boundaries; no kernel-proof claim."""

import copy
import json
from pathlib import Path
import tarfile
import unittest

from lark_kernels import ptx_rotary as reader
from lark_kernels.ir import Refusal


ROOT = Path(__file__).resolve().parents[1]


def inputs():
    names = ("cases/rope/kernel/kernel.ptx", "cases/rope/original/reference.py",
             "cases/rope/original/task.json")
    with tarfile.open(ROOT / "reproduction/ptx/results/full-size-compilation-v1/raw.tar.gz") as archive:
        return [archive.extractfile(name).read().decode() for name in names]


class PtxRotaryReaderTests(unittest.TestCase):
    def test_closed_tensor_AST_and_generated_statement_bind_the_complete_reference(self):
        prepared = reader.prepare_certificate(*inputs())
        body = prepared[2]
        self.assertEqual(body, reader.REFERENCE)
        self.assertIsNot(body, reader.REFERENCE)
        rendered = reader.render(*prepared)
        self.assertIn("LarkPtxRotary.Kernel.Correct ops program (spec ops)", rendered)
        self.assertIn("(.select 2 0", rendered)
        self.assertIn("(.select 2 1", rendered)
        self.assertIn("(.stackLast", rendered)
        self.assertIn("(.reshape [256, 128]", rendered)
        self.assertIn("extractReference ops input referenceBody", rendered)
        self.assertIn("reference_denotation", rendered)
        altered = copy.deepcopy(body)
        altered[1][1][0] = True
        with self.assertRaises(Refusal):
            reader.lean_reference(altered)
        altered = copy.deepcopy(body)
        altered[1][2][1][0] = "add"
        with self.assertRaises(Refusal):
            reader.lean_reference(altered)
        self.assertEqual(body, reader.REFERENCE)

    def test_complete_source_predicates_branches_shape_and_launch_are_preserved(self):
        source, reference, contract = inputs()
        task, parsed = reader.prepare(source, reference, contract)
        self.assertEqual(parsed.readback(), source)
        self.assertEqual(len(parsed.instructions), 51)
        self.assertEqual(len(parsed.registers), 52)
        self.assertEqual(parsed.labels, {"$L__BB0_2": 31, "$L__BB0_1": 41, "$L__BB0_3": 50})
        self.assertEqual(parsed.instructions[18:22], [
            ["compareEqBits32", 1, 6, ["imm", 1]], ["predicateLiteral", 2, False],
            ["predicateXor", 3, 1, 2], ["predicateNot", 4, 3]])
        self.assertEqual(parsed.instructions[29:31], [["branch", 4, 31], ["branchAlways", 41]])
        self.assertEqual(parsed.instructions[40], ["branchAlways", 50])
        self.assertEqual([b.shape for b in task.buffers], [(256, 128), (256, 64), (256, 64), (256, 128)])
        self.assertEqual((task.grid, task.block, task.warp), (32768, 1, 32))
        self.assertEqual(task.fuel, (8, 1, 1, 1))
        self.assertIn("(.predicateLiteral 2 false)", parsed.lean_program())

    def test_changed_predicates_and_arithmetic_change_the_formal_instruction_data(self):
        data = inputs()
        original = reader.prepare(*data)[1]
        for source in [data[0].replace("%p2, 0;", "%p2, 1;"),
                       data[0].replace("mul.rn.f32", "add.rn.f32", 1)]:
            with self.subTest(source=source):
                changed = reader.prepare(source, *data[1:])[1]
                self.assertEqual(changed.readback(), source)
                self.assertNotEqual(changed.instructions, original.instructions)
                self.assertNotEqual(changed.lean_program(), original.lean_program())
        commented = "// sorry; native_decide; set_option maxHeartbeats 0\n" + data[0]
        parsed = reader.prepare(commented, *data[1:])[1]
        self.assertEqual(parsed.readback(), commented)
        self.assertEqual(parsed.instructions, original.instructions)
        self.assertNotIn("sorry", parsed.lean_program())

    def test_complete_reference_module_and_original_operator_are_required(self):
        source, reference, contract = inputs()
        for altered in [reference.replace("-", "+", 1), reference.replace("dim=-1", "dim=0"),
                        reference.replace("select(2,0)", "select(2,1)"),
                        reference + "\nprint('side effect')\n",
                        reference.replace(".half()", "")]:
            with self.subTest(reference=altered), self.assertRaises(Refusal):
                reader.prepare(source, altered, contract)

    def test_labels_register_aliases_literal_values_and_trailing_entries_are_refused(self):
        source, reference, contract = inputs()
        for altered in [source.replace("$L__BB0_1;", "$L__missing;"),
                        source.replace("$L__BB0_1:", "$L__BB0_1:\n$L__BB0_1:"),
                        source.replace("%p4", "%p04"), source.replace("%p2, 0;", "%p2, 2;"),
                        source.replace("%p2, 0;", "%r2, 0;"),
                        source + "\n.visible .entry hidden() { ret; }\n"]:
            with self.subTest(source=altered), self.assertRaises(Refusal):
                reader.prepare(altered, reference, contract)

    def test_shape_dtype_geometry_and_cuda_fuel_cannot_be_reduced_or_increased(self):
        source, reference, contract = inputs()
        for key, value in [("fuel", [9, 1, 1, 1]), ("fuel", [8, True, 1, 1]),
                           ("launch", {"grid": 32768, "block": 2, "warp": 32}),
                           ("launch", {"grid": 32768, "block": 1, "warp": 64})]:
            changed = json.loads(contract)
            changed[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(Refusal):
                reader.prepare(source, reference, json.dumps(changed))
        changed = json.loads(contract)
        for buffer, shape in zip(changed["buffers"], [[1, 2], [1, 1], [1, 1], [1, 2]], strict=True):
            buffer["shape"] = shape
        changed["launch"]["grid"] = 2
        with self.assertRaises(Refusal):
            reader.prepare(source, reference, json.dumps(changed))
        changed = json.loads(contract)
        changed["buffers"][0]["dtype"] = "float32"
        with self.assertRaises(Refusal):
            reader.prepare(source, reference, json.dumps(changed))

    def test_constructor_injection_boolean_indices_and_capacity_changes_are_refused(self):
        for instruction in [["ret\naxiom h : False"], ["predicateLiteral", True, False],
                            ["predicateLiteral", 2, 1], ["predicateNot", 2, False],
                            ["predicateXor", 1, 2, 256], ["predicateXor", 1, 2, -1],
                            ["branchAlways", False], ["branchAlways", 256],
                            ["compareEqBits32", 1, 2, ["imm", True]],
                            ["compareEqBits32", 1, 2, ["reg", 256]],
                            ["compareEqBits32", 1, 2, ["imm", 2**31]]]:
            with self.subTest(instruction=instruction), self.assertRaises(Refusal):
                reader.lean_instruction(instruction)
        source, reference, contract = inputs()
        enlarged = source.replace("ret;", "mov.pred %p2, 0;\n" * 260 + "ret;")
        with self.assertRaises(Refusal):
            reader.prepare(enlarged, reference, contract)


if __name__ == "__main__":
    unittest.main()
