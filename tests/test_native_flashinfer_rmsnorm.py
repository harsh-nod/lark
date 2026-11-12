import copy
import json
from pathlib import Path
import unittest

from lark_kernels import native_flashinfer_rmsnorm as native
from lark_kernels.ir import Refusal, Task

CASE = Path(__file__).resolve().parents[1] / "reproduction/production_flashinfer_rmsnorm/cases/native_16384"


class NativeFlashInferContractTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((CASE / "task.json").read_text())

    def parse(self, data):
        return native.parse_task(json.dumps(data))

    def rows(self, n):
        data = copy.deepcopy(self.data)
        data["buffers"][0]["shape"][0] = data["buffers"][1]["shape"][0] = n
        data["launch"]["grid"] = n
        return data

    def test_maximum_supported_index_is_signed_int32(self):
        task = self.parse(self.rows(131072))
        self.assertEqual(task.buffers[0].size - 1, 2**31 - 1)
        for n in (0, 131073, True):
            with self.subTest(rows=n), self.assertRaises(Refusal):
                self.parse(self.rows(n))

    def test_signature_geometry_and_fuel_are_closed(self):
        for change in (lambda d: d.update(entry="other"),
                       lambda d: d.update(language="cuda"),
                       lambda d: d["launch"].update(block=512),
                       lambda d: d["launch"].update(warp=32),
                       lambda d: d["launch"].update(grid=True),
                       lambda d: d.update(fuel=[512, 8, 3, True]),
                       lambda d: d["buffers"][0].update(role="inout"),
                       lambda d: d["buffers"][2].update(dtype="float32"),
                       lambda d: d.update(source_certificates=1)):
            data = copy.deepcopy(self.data)
            change(data)
            with self.subTest(data=data), self.assertRaises(Refusal):
                self.parse(data)

    def test_ordinary_parser_does_not_accept_native_geometry(self):
        self.parse(self.data)
        with self.assertRaises(Refusal):
            Task.parse(json.dumps(self.data))

    def test_reference_axis_weight_and_epsilon_are_bound(self):
        text = (CASE / "reference.py").read_text()
        native.check_reference("# independent formatting\n" + text)
        for changed in (text.replace("dim=1", "dim=0"),
                        text.replace("1e-5", "1e-4"),
                        text.replace("0.0 + weight", "1.0 + weight"),
                        text.replace(".half()", "")):
            with self.subTest(changed=changed), self.assertRaises(Refusal):
                native.check_reference(changed)


if __name__ == "__main__":
    unittest.main()
