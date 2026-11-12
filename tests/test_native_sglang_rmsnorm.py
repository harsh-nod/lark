import json
from pathlib import Path
import unittest

from lark_kernels import collective, native_sglang_rmsnorm as native
from lark_kernels.ir import Refusal, Task


CASE = Path(__file__).resolve().parents[1] / "reproduction/production_sglang_rmsnorm/cases/native_fixed"


class NativeSglangContractTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((CASE / "task.json").read_text())
        self.source = (CASE / "kernel.hip").read_text()
        self.task = native.parse_task(json.dumps(self.data))

    def test_private_half_caches_are_typed_and_source_roundtrips(self):
        translated = native.translate(self.source, self.task)
        self.assertEqual(translated.readback(), self.source)
        self.assertEqual([size for _, size in translated.locals], [16, 16, 16])
        changes = [
            self.source.replace("__half input_values[16]", "float input_values[16]"),
            self.source.replace("__half2float(input_values[square_slot])", "input_values[square_slot]"),
            self.source.replace("__float2half(result_x)", "result_x"),
            self.source.replace("__half input_values[16]", "__half input_values[8]"),
        ]
        for changed in changes:
            with self.subTest(changed=changed[:50]), self.assertRaises(Refusal):
                native.translate(changed, self.task)

    def test_private_half_arrays_remain_opt_in(self):
        with self.assertRaises(Refusal):
            collective.Reader(self.source, self.task).read()
        with self.assertRaises(Refusal):
            Task.parse(json.dumps(self.data))

    def test_signed_address_bound_and_boolean_dimensions(self):
        for rows in (1, 255, 131072):
            data = json.loads(json.dumps(self.data))
            data["launch"]["grid"] = rows
            for buffer in data["buffers"][:2]:
                buffer["shape"][0] = rows
            self.assertEqual(native.parse_task(json.dumps(data)).grid, rows)
        self.assertEqual(131072 * native.WIDTH - 1, 2 ** 31 - 1)
        for rows in (0, 131073, True):
            data = json.loads(json.dumps(self.data))
            data["launch"]["grid"] = rows
            for buffer in data["buffers"][:2]:
                buffer["shape"][0] = rows
            with self.subTest(rows=rows), self.assertRaises(Refusal):
                native.parse_task(json.dumps(data))

    def test_reference_is_bound_and_not_executed(self):
        reference = (CASE / "reference.py").read_text()
        native.check_reference(reference)
        for changed in (reference.replace("dim=1", "dim=0"),
                        reference.replace("1e-5", "1e-4"),
                        reference.replace("weight.float()", "1.0"),
                        reference + "\nraise RuntimeError('must not execute')\n"):
            with self.assertRaises(Refusal):
                native.check_reference(changed)


if __name__ == "__main__":
    unittest.main()
