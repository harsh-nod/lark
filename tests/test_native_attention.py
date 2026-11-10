import json
from pathlib import Path
import unittest

from lark_kernels import native_attention as native
from lark_kernels.frontend import Reader
from lark_kernels.ir import Refusal, Task, node

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "reproduction/online_attention/cases/native_fp16"


class NativeAttentionTests(unittest.TestCase):
    def test_complete_source_contract_and_readback(self):
        task = native.parse_task((CASE / "task.json").read_text())
        source = (CASE / "kernel.hip").read_bytes().decode().replace("\n", "\r\n")
        tr = native.translate(source, task)
        self.assertEqual(tr.readback(), source)
        self.assertEqual(len(tr.program), 91)
        self.assertEqual(tr.shared, [("qi", 8192), ("kj", 8192), ("vj", 8192), ("scores", 1024)])
        self.assertEqual(tr.locals, [("running_m", 4), ("running_l", 4)])
        self.assertEqual([i for i, op in enumerate(tr.program) if op.op == "barrier"], [20, 87])
        native.check_reference((CASE / "reference.py").read_text(), task)
        with self.assertRaises(Refusal):
            native.check_reference((CASE / "reference.py").read_text().replace("16.0", "8.0"), task)

    def test_contract_extremes_and_refusals(self):
        data = json.loads((CASE / "task.json").read_text())
        for groups in (1, 3, 65535):
            trial = json.loads(json.dumps(data))
            for b in trial["buffers"]:
                b["shape"][0] = groups
            trial["launch"]["grid"] = groups
            task = native.parse_task(json.dumps(trial))
            self.assertLess(task.buffers[0].size, 2**31)
            self.assertEqual(task.grid, groups)
        for path, value in [(("launch", "block"), 64), (("launch", "warp"), 32),
                            (("fuel", 2), 8), (("buffers", 2, "dtype"), "float32"),
                            (("buffers", 0, "shape", 0), True),
                            (("buffers", 0, "shape", 0), 65536)]:
            trial = json.loads(json.dumps(data))
            at = trial
            for key in path[:-1]:
                at = at[key]
            at[path[-1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(Refusal):
                native.parse_task(json.dumps(trial))
        with self.assertRaises(Refusal):
            Task.parse(json.dumps(data))
        task = native.parse_task(json.dumps(data))
        with self.assertRaises(Refusal):
            Reader((CASE / "kernel.hip").read_text(), task).read()

    def private_case(self, changed=""):
        data = {"name": "private", "entry": "private_kernel", "language": "hip",
                "buffers": [{"name": "out", "role": "output", "shape": [32], "dtype": "float32"},
                            {"name": "input", "role": "input", "shape": [32], "dtype": "float32"}],
                "launch": {"grid": 1, "block": 32, "warp": 64}, "fuel": [16, 1, 2, 1]}
        source = '''extern "C" __global__ void private_kernel(float* out, const float* input) {
  float scratch[1];
  scratch[0] = input[threadIdx.x];
  __syncthreads();
  out[threadIdx.x] = scratch[0];
}'''
        if changed == "uninitialized":
            source = source.replace("scratch[0] = input[threadIdx.x];", "")
        if changed == "bounds":
            source = source.replace("= scratch[0]", "= scratch[1]")
        task = Task.parse(json.dumps(data))
        return task, source

    def test_private_values_survive_other_threads_and_a_barrier(self):
        task, source = self.private_case()
        tr = native.NativeReader(source, task).read()
        m = native.NativeMachine(task, tr).run()
        self.assertEqual(m.outputs(), [node("input", 1, i) for i in range(32)])
        self.assertIsNone(m.race())
        self.assertEqual({a.location[1] for a in m.trace if a.location[0] == "local"}, set(range(32)))
        erased = native.AccessPreflight(task, tr)
        for method, code in ((erased.outputs, "values-erased"), (erased.race, "trace-erased")):
            with self.assertRaises(Refusal) as error:
                method()
            self.assertEqual(error.exception.code, code)
        with self.assertRaises(Refusal):
            Reader(source, task).read()

    def test_private_uninitialized_and_bounds_faults(self):
        for mutation, code in (("uninitialized", "uninitialized"), ("bounds", "bounds")):
            task, source = self.private_case(mutation)
            tr = native.NativeReader(source, task).read()
            with self.subTest(mutation=mutation), self.assertRaises(Refusal) as error:
                native.NativeMachine(task, tr).run()
            self.assertEqual(error.exception.code, code)


if __name__ == "__main__":
    unittest.main()
