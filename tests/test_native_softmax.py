import json
from pathlib import Path
import unittest

from lark_kernels import native_softmax as native
from lark_kernels.frontend import Reader as OrdinaryReader
from lark_kernels.ir import Refusal, Task

CASE = Path(__file__).resolve().parents[1] / "reproduction/production_softmax/cases/native_race"


class NativeSoftmaxTests(unittest.TestCase):
    def setUp(self):
        self.raw = (CASE / "task.json").read_text()
        self.task = native.parse_task(self.raw)

    def test_closed_contract_preserves_ordinary_limits(self):
        with self.assertRaises(Refusal):
            Task.parse(self.raw)
        for rows in (1, 3, 255, 4095, 8192, native.MAX_ROWS):
            data = json.loads(self.raw)
            data["launch"]["grid"] = rows
            for buffer in data["buffers"]:
                buffer["shape"][0] = rows
            self.assertEqual(native.parse_task(json.dumps(data)).grid, rows)
        for rows in (0, True, native.MAX_ROWS + 1):
            data = json.loads(self.raw)
            data["launch"]["grid"] = rows
            for buffer in data["buffers"]:
                buffer["shape"][0] = rows
            with self.subTest(rows=rows), self.assertRaises(Refusal):
                native.parse_task(json.dumps(data))
        for field, value in (("warp", 32), ("block", 32)):
            data = json.loads(self.raw)
            data["launch"][field] = value
            with self.subTest(field=field), self.assertRaises(Refusal):
                native.parse_task(json.dumps(data))

    def test_infinity_seed_is_explicit_and_cannot_be_shadowed(self):
        code = '''extern "C" __global__ void softmax_forward_kernel7(__half* out, const __half* inp) {
float maximum = -INFINITY;
}'''
        tr = native.translate(code, self.task)
        self.assertEqual(tr.program[0].args[1].args, (-1, native.NEG_INF_SEED_DENOMINATOR))
        self.assertGreater(native.NEG_INF_SEED_DENOMINATOR, 0)
        with self.assertRaises(Refusal):
            OrdinaryReader(code, self.task).read()
        changed = code.replace("float maximum", "float INFINITY = 2.0f;\nfloat maximum")
        with self.assertRaises(Refusal):
            native.translate(changed, self.task)

    def test_private_arrays_use_thread_ownership(self):
        code = '''extern "C" __global__ void softmax_forward_kernel7(__half* out, const __half* inp) {
float regs[8];
int t = threadIdx.x;
regs[0] = 0.0f;
float value = regs[0];
out[t] = __float2half(value);
}'''
        tr = native.translate(code, self.task)
        machine = native.Machine(self.task, tr).run()
        private = [a for a in machine.trace if a.location[0] == "local"]
        self.assertEqual(len(private), 2048)
        self.assertTrue(all(a.thread == a.location[1] for a in private))
        with self.assertRaises(Refusal):
            native.translate(code.replace("regs[8]", "regs[7]"), self.task)

    def test_full_sources_read_back_and_retain_both_helper_reductions(self):
        for name in ("native_race", "native_fixed"):
            case = CASE.parent / name
            code = (case / "kernel.hip").read_text()
            tr = native.translate(code, self.task)
            self.assertEqual(tr.readback(), code)
            self.assertEqual(tr.locals, [("exp_regs", 8), ("norm_regs", 8)])
            self.assertEqual(tr.shared, [("maxvals", 32), ("sumvals", 32)])
            shuffles = [i.args[0] for i in tr.program if i.op == "shuffle"]
            self.assertEqual(shuffles, ["down"] * 5 + ["xor"] * 5)
            self.assertEqual(sum(i.op == "barrier" for i in tr.program), 4)


if __name__ == "__main__":
    unittest.main()
