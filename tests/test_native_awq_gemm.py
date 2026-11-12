import json
import unittest

from lark_kernels import mfma, native_awq_gemm as native
from lark_kernels.ir import Refusal
from reproduction.production_awq_gemm.symbolic_reference import output_expression


class NativeAwqTests(unittest.TestCase):
    def source(self, m=1, k=32, n=64):
        shape = native.Shape(m, k, n)
        task = native.parse_task(json.dumps(native.task_data(shape)))
        return task, native.kernel_source(shape)

    def test_both_typed_shared_tiles_preserve_source_and_storage_types(self):
        for n in (64, 128):
            with self.subTest(n=n):
                task, source = self.source(n=n)
                tr = native.translate(source, task)
                self.assertEqual(tr.readback(), source)
                self.assertEqual(tr.shared, [("tileA", 640), ("tileB", 32*(n+8))])
                with self.assertRaises(Refusal):
                    mfma.translate(source, task)
                for changed in (
                    source.replace("__float2half(acc0[0])", "acc0[0]", 1),
                    source.replace("__shared__ _Float16", "__shared__ float", 1),
                    source.replace("H4 left0", "F4 left0", 1),
                ):
                    with self.assertRaises(Refusal):
                        native.translate(changed, task)

    def test_actual_matrix_runs_match_dense_indexed_source_order(self):
        for n in (64, 128):
            with self.subTest(n=n):
                task, source = self.source(n=n)
                machine = native.Machine(task, native.translate(source, task)).run()
                self.assertIsNone(machine.race())
                self.assertEqual(machine.outputs(), [output_expression(1, 32, n, 0, col) for col in range(n)])
                self.assertEqual({thread.epoch[1] for thread in machine.threads}, {2})

    def test_matrix_operand_and_reused_shared_tile_changes_are_detected(self):
        task, source = self.source(k=64)
        wrong = source.replace("(left0, right0_0, acc0,", "(left0, left0, acc0,", 1)
        self.assertNotEqual(wrong, source)
        machine = native.Machine(task, native.translate(wrong, task)).run()
        self.assertNotEqual(machine.outputs()[0], output_expression(1, 64, 64, 0, 0))
        missing = source.replace("    __syncthreads();\n", "", 1)
        machine = native.Machine(task, native.translate(missing, task)).run()
        self.assertIsNotNone(machine.race())


if __name__ == "__main__":
    unittest.main()
