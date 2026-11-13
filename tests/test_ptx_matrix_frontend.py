"""Read the actual frozen full-size GEMM PTX and reject unsafe profile changes."""

import hashlib
import json
from pathlib import Path
import unittest

from lark_kernels.ir import Refusal
from reproduction.ptx.matrix_frontend import lean_instruction, prepare


FIXTURE = Path(__file__).resolve().parents[1] / 'reproduction/ptx/cases/full-size-gemm'


class PtxMatrixFrontendTests(unittest.TestCase):
    def setUp(self):
        self.source = (FIXTURE / 'kernel.ptx').read_text()
        self.reference = (FIXTURE / 'reference.py').read_text()
        self.contract = (FIXTURE / 'task.json').read_text()

    def test_entire_actual_compiler_output_and_original_contract_are_retained(self):
        bindings = json.loads((FIXTURE / 'source-bindings.json').read_text())
        for name, digest in bindings.items():
            self.assertEqual(hashlib.sha256((FIXTURE / name).read_bytes()).hexdigest(), digest)
        task, parsed = prepare(self.source, self.reference, self.contract)
        self.assertEqual(parsed.readback(), self.source)
        self.assertEqual(len(parsed.instructions), 171)
        self.assertEqual(len(parsed.registers), 182)
        self.assertEqual(parsed.labels, {'$L__BB0_1': 47})
        self.assertEqual(parsed.instructions[164], ['branch', 1, 47])
        self.assertEqual((task.grid, task.block, task.warp, task.fuel), (32768, 1, 32, (1030, 1, 1, 1)))
        self.assertEqual([b.shape for b in task.buffers], [(64, 256), (256, 512), (64, 512)])
        self.assertIn('(.andBits32 10 7 (.imm (-512)))', parsed.lean_program())

    def test_smaller_compatible_shape_cannot_replace_the_full_size_profile(self):
        task = json.loads(self.contract)
        task['buffers'][0]['shape'][1] = task['buffers'][1]['shape'][0] = 128
        task['fuel'][0] = 518
        with self.assertRaisesRegex(Refusal, 'unchanged 64x256'):
            prepare(self.source, self.reference, json.dumps(task))

    def test_unchanged_cuda_fuel_is_checked_with_numeric_types(self):
        for fuel in ([1031, 1, 1, 1], [1030, True, 1, 1]):
            with self.subTest(fuel=fuel):
                task = json.loads(self.contract)
                task['fuel'] = fuel
                with self.assertRaises(Refusal):
                    prepare(self.source, self.reference, json.dumps(task))

    def test_signed_mask_and_new_register_banks_are_parsed_as_typed_data(self):
        source = self.source.replace('shr.s32 \t%r5', 'shr.s32 \t%rd5')
        self.assertNotEqual(source, self.source)
        with self.assertRaises(Refusal):
            prepare(source, self.reference, self.contract)

    def test_undefined_actual_backward_target_is_refused(self):
        source = self.source.replace('bra \t$L__BB0_1;', 'bra \t$missing;')
        self.assertNotEqual(source, self.source)
        with self.assertRaisesRegex(Refusal, 'undefined or out-of-range branch label'):
            prepare(source, self.reference, self.contract)

    def test_extra_program_or_reference_statements_are_refused(self):
        for source, reference in ((self.source + '\nret;\n', self.reference),
                                  (self.source, self.reference + '\nprint("extra")\n')):
            with self.subTest(source_extra=source != self.source):
                with self.assertRaises(Refusal):
                    prepare(source, reference, self.contract)

    def test_changed_matrix_stride_remains_visible_and_is_not_a_certificate(self):
        _, original = prepare(self.source, self.reference, self.contract)
        source = self.source.replace('%rd48, %rd48, 16384;', '%rd48, %rd48, 1024;')
        self.assertNotEqual(source, self.source)
        _, changed = prepare(source, self.reference, self.contract)
        self.assertEqual(changed.readback(), source)
        self.assertNotEqual(changed.instructions, original.instructions)
        self.assertNotEqual(changed.lean_program(), original.lean_program())

    def test_constructor_data_cannot_inject_lean_or_use_boolean_integers(self):
        cases = [
            ['andBits32', True, 7, ['imm', -512]],
            ['andBits32', 10, 7, ['imm', -512.0]],
            ['andBits32', 10, 7, ['reg', '1); axiom bad : False']],
            ['shiftRightSigned32', 5, 1, True],
            ['shiftRightUnsigned32', 5, 1, 2**32],
            ['mulWideUnsigned32', 256, 1, 2],
            ['base', 'by sorry'],
        ]
        for value in cases:
            with self.subTest(value=value):
                with self.assertRaises(Refusal):
                    lean_instruction(value)


if __name__ == '__main__':
    unittest.main()
