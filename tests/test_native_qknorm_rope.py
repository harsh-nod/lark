"""Closed fused-Q/K host contract, trusted reference boundary and input safety."""

import json
from pathlib import Path
import unittest

from lark_kernels import collective, native_qknorm_rope as native
from lark_kernels import native_qknorm_rope_certificate as certificate
from lark_kernels.ir import Refusal, Task

CASES = Path(__file__).resolve().parents[1] / "reproduction/production_qknorm_rope/cases"


class NativeQKNormRopeTests(unittest.TestCase):
    def test_native_grid_head_mapping_and_signed_bounds_at_maximum_rows(self):
        for layout in native.LAYOUTS:
            raw = json.loads((CASES / layout / "task.json").read_text())
            for rows in (1, 3, 256, 65535):
                raw["launch"]["grid"] = rows * 5
                for b in raw["buffers"]:
                    if len(b["shape"]) > 1:
                        b["shape"][0] = rows
                contract = native.parse_task(json.dumps(raw))
                self.assertEqual(contract.task.grid * contract.task.block, rows * 40 * 32)
                self.assertLess(contract.task.buffers[1].size, 2**31)
                self.assertEqual(contract.task.buffers[0].size, rows * 40 * 128)
                with self.assertRaises(Refusal):
                    Task.parse(json.dumps({k: v for k, v in raw.items() if k != "rotary_layout"}))

    def test_wrong_roles_shapes_geometry_flags_and_boolean_dimensions_refused(self):
        changes = [lambda r: r.update(unchecked_aliases=True), lambda r: r.update(rotary_layout="unknown"),
                   lambda r: r["launch"].update(grid=True), lambda r: r["launch"].update(block=512),
                   lambda r: r["launch"].update(warp=32), lambda r: r["buffers"][0].update(role="inout"),
                   lambda r: r["buffers"][1]["shape"].__setitem__(1, 40),
                   lambda r: r["buffers"][1]["shape"].__setitem__(0, True),
                   lambda r: r["buffers"][2].update(dtype="float32"),
                   lambda r: r["buffers"][3]["shape"].__setitem__(0, 64),
                   lambda r: r["buffers"][0]["shape"].__setitem__(0, 65536),
                   lambda r: r["fuel"].__setitem__(1, True)]
        for i, change in enumerate(changes):
            raw = json.loads((CASES / "interleaved/task.json").read_text())
            change(raw)
            with self.subTest(control=i), self.assertRaises(Refusal):
                native.parse_task(json.dumps(raw))

    def test_reference_mean_weight_order_epsilon_and_rotation_are_bound(self):
        for layout in native.LAYOUTS:
            text = (CASES / layout / "reference.py").read_text()
            for changed in (text.replace("dim=-1", "dim=1"), text.replace("1e-5", "1e-4"),
                            text.replace("x * (scale * weight.float())", "(x * scale) * weight.float()"),
                            text.replace("qkv[:, 32:40, :]", "qkv[:, 40:48, :]")):
                with self.subTest(layout=layout), self.assertRaises(Refusal):
                    native.check_reference(changed, layout)

    def test_native_fence_support_does_not_weaken_the_ordinary_hip_reader(self):
        case = CASES / "split-half"
        contract = native.parse_task((case / "task.json").read_text())
        source = (case / "kernel.hip").read_text()
        native.translate(source, contract)
        with self.assertRaisesRegex(Refusal, "warp-mask"):
            collective.Reader(source, contract.task).read()

    def test_split_half_cannot_inherit_the_interleaved_real_certificate(self):
        case = CASES / "split-half"
        with self.assertRaisesRegex(Refusal, "complete exact-real certificate currently requires interleaved"):
            certificate.prepare(*((case / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")))

    def test_write_to_the_readonly_qkv_is_refused_during_translation(self):
        case = CASES / "interleaved"
        contract = native.parse_task((case / "task.json").read_text())
        source = (case / "kernel.hip").read_text().replace("output[out0] =", "qkv[out0] =")
        with self.assertRaisesRegex(Refusal, "const"):
            native.translate(source, contract)


if __name__ == "__main__":
    unittest.main()
