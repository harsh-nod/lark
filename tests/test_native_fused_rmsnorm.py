import json
from pathlib import Path
import unittest

from lark_kernels import native_fused_rmsnorm as native
from lark_kernels.ir import Refusal, Task, node
from lark_kernels.machine import Machine

CASE = Path(__file__).resolve().parents[1] / "reproduction/production_fused_rmsnorm/cases/native_16384"


class NativeFusedRmsNormTests(unittest.TestCase):
    def setUp(self):
        self.raw = (CASE / "task.json").read_text()
        self.source = (CASE / "kernel.hip").read_text()
        self.contract = native.parse_task(self.raw)

    def test_inout_initialization_and_ordinary_refusal(self):
        with self.assertRaises(Refusal):
            Task.parse(self.raw)
        tr = native.translate(self.source, self.contract)
        ordinary = Machine(self.contract.task, tr)
        seeded = native.Machine(self.contract, tr)
        for b in (0, 1):
            self.assertNotIn(("global", 0, b, 0), ordinary.memory)
            self.assertEqual(seeded.memory["global", 0, b, 0], node("input", b, 0))
        self.assertEqual(seeded.memory["global", 0, 2, 0], node("input", 2, 0))

    def test_exact_readback_and_shared_layout(self):
        tr = native.translate(self.source, self.contract)
        self.assertEqual(tr.readback(), self.source)
        self.assertEqual(tr.shared, [("partial", 32), ("unrounded", 16384)])
        self.assertEqual(len(tr.program), 72)
        self.assertEqual([i for i, x in enumerate(tr.program) if x.op == "barrier"], [35, 50])

    def test_closed_contract_and_reference(self):
        for path, value in [(("buffers", 0, "role"), "output"),
                            (("buffers", 1, "role"), "input"),
                            (("buffers", 0, "shape", 0), True),
                            (("buffers", 1, "shape", 1), 8192),
                            (("launch", "warp"), 32),
                            (("launch", "block"), 512),
                            (("fuel", 0), 513)]:
            data = json.loads(self.raw)
            current = data
            for key in path[:-1]:
                current = current[key]
            current[path[-1]] = value
            with self.subTest(path=path), self.assertRaises(Refusal):
                native.parse_task(json.dumps(data))
        reference = (CASE / "reference.py").read_text()
        native.check_reference(reference)
        with self.assertRaises(Refusal):
            native.check_reference(reference.replace("return output, x.half()", "return output, residual"))

    def test_shape_extremes(self):
        for rows in (1, 3, 64, 255):
            data = json.loads(self.raw)
            data["launch"]["grid"] = rows
            for b in data["buffers"][:2]:
                b["shape"][0] = rows
            contract = native.parse_task(json.dumps(data))
            self.assertEqual(contract.task.grid, rows)
        data["launch"]["grid"] = 256
        for b in data["buffers"][:2]:
            b["shape"][0] = 256
        with self.assertRaises(Refusal):
            native.parse_task(json.dumps(data))

    def test_finite_accesses_and_missing_barrier_or_ownership(self):
        tr = native.translate(self.source, self.contract)
        m = native.AccessPreflight(self.contract, tr)
        m.run()
        self.assertEqual(m.accesses, 115777)
        self.assertTrue(all(t.pc == 71 and t.epoch == [0, 2, 0] for t in m.threads))
        with self.assertRaises(Refusal):
            m.outputs()
        with self.assertRaises(Refusal):
            m.race()
        variants = [
            self.source.replace("__syncthreads();", "", 1),
            self.source.replace("unrounded[column] = x", "unrounded[component] = x"),
            self.source.replace("if (lane == 0) { partial[warp] = sum; }", "partial[warp] = sum;"),
            self.source.replace("float value = unrounded[output_column];",
                                "float value = __half2float(residual[output_address]);"),
        ]
        for source in variants:
            self.assertNotEqual(source, self.source)
            with self.subTest(source=source[-120:]), self.assertRaises(Refusal):
                native.AccessPreflight(self.contract, native.translate(source, self.contract)).run()


if __name__ == "__main__":
    unittest.main()
