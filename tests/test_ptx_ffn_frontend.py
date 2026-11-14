"""Preparation guards for original-size FFN inputs; these execute no Lean proof."""

import json
from pathlib import Path
import unittest

from lark_kernels import ptx_ffn
from lark_kernels.ir import Refusal


INPUTS = Path(__file__).resolve().parents[1] / "reproduction/ptx/full-size/ffn"


class CompiledFeedForwardPreparationTests(unittest.TestCase):
    def setUp(self):
        self.sources = [(INPUTS / stage / "kernel.ptx").read_text() for stage in ("up", "down")]
        self.contracts = [(INPUTS / stage / "task.json").read_text() for stage in ("up", "down")]
        self.reference = (INPUTS / "reference.py").read_text()

    def prepare(self):
        return ptx_ffn.prepare(*self.sources, self.reference, *self.contracts)

    def test_both_full_stages_roundtrip_with_original_shapes_geometry_and_fuel(self):
        tasks, parsed, body = self.prepare()
        self.assertEqual([len(t.instructions) for t in parsed], [173, 171])
        self.assertEqual([t.readback() for t in parsed], self.sources)
        self.assertEqual([tuple(t.fuel) for t in tasks], [(1030, 1, 1, 1), (4102, 1, 1, 1)])
        self.assertEqual([t.grid for t in tasks], [65536, 16384])
        self.assertEqual(tasks[0].buffers[2].shape, (64, 1024))
        self.assertEqual(tasks[1].buffers[0].shape, (64, 1024))
        self.assertEqual(body, ptx_ffn.REFERENCE)

    def test_intermediate_roundtrip_and_reference_operation_order_are_required(self):
        for old, new in [(".relu().half().float()", ".relu()"),
                         (".relu().half().float()", ".half().float().relu()"),
                         ("down.float()", "down")]:
            with self.subTest(change=new), self.assertRaisesRegex(Refusal, "FP16-intermediate"):
                ptx_ffn.prepare(*self.sources, self.reference.replace(old, new), *self.contracts)

    def test_entire_reference_module_is_bound_and_returned_ast_is_independent(self):
        with self.assertRaises(Refusal):
            ptx_ffn.reference_body(self.reference + "\nraise RuntimeError('extra module statement')\n")
        body = ptx_ffn.reference_body(self.reference)
        body[1][0] = "altered"
        self.assertEqual(ptx_ffn.reference_body(self.reference), ptx_ffn.REFERENCE)

    def test_reference_constructor_preserves_both_stores_and_all_four_load_conversions(self):
        body = ptx_ffn.reference_body(self.reference)
        encoded = ptx_ffn.lean_reference(body)
        self.assertEqual(encoded.count("(.matmul "), 2)
        self.assertEqual(encoded.count("(.toHalf "), 2)
        self.assertEqual(encoded.count("(.fromHalf "), 4)
        self.assertEqual(encoded.count("(.relu "), 1)
        body[1][1][1][0] = "fromHalf"
        with self.assertRaises(Refusal):
            ptx_ffn.lean_reference(body)

    def test_original_long_second_stage_fuel_cannot_be_reduced(self):
        task = json.loads(self.contracts[1])
        task["fuel"][0] = 1030
        self.contracts[1] = json.dumps(task)
        with self.assertRaisesRegex(Refusal, "fuel"):
            self.prepare()

    def test_changed_full_shape_grid_and_dtype_are_refused(self):
        for stage, field in [(0, "shape"), (1, "grid"), (0, "dtype")]:
            task = json.loads((INPUTS / ("up" if stage == 0 else "down") / "task.json").read_text())
            if field == "shape":
                task["buffers"][2]["shape"][1] = 512
            elif field == "grid":
                task["launch"]["grid"] //= 2
            else:
                task["buffers"][2]["dtype"] = "float32"
            contracts = self.contracts.copy()
            contracts[stage] = json.dumps(task)
            with self.subTest(stage=stage, field=field), self.assertRaises(Refusal):
                ptx_ffn.prepare(*self.sources, self.reference, *contracts)

    def test_intermediate_cannot_be_rebound_to_another_named_buffer(self):
        task = json.loads(self.contracts[1])
        task["buffers"][0]["name"] = "other_hidden"
        self.contracts[1] = json.dumps(task)
        with self.assertRaisesRegex(Refusal, "unchanged full-size"):
            self.prepare()

    def test_extra_source_is_not_ignored_and_stage_entry_binding_is_required(self):
        self.sources[0] += "\nret;\n"
        with self.assertRaises(Refusal):
            self.prepare()
        self.sources[0] = (INPUTS / "up/kernel.ptx").read_text()
        self.sources[1] = self.sources[0]
        with self.assertRaises(Refusal):
            self.prepare()


if __name__ == "__main__":
    unittest.main()
