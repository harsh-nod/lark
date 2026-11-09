import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, convolution
from lark_kernels.ir import Refusal, Task

CASES = Path(__file__).resolve().parents[1] / "reproduction/convolution/cases/hip"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class ConvolutionTests(unittest.TestCase):
    def sources(self, family):
        return tuple(
            (CASES / family / f).read_text() for f in ("kernel.hip", "reference.py", "task.json")
        )

    def test_full_profiles_and_group_contracts_preserve_bounded_limits(self):
        for family, dims in [("conv2d", (32, 8, 8, 3, 1)), ("depthwise_conv", (32, 32, 16, 5, 32))]:
            source, ref, raw = self.sources(family)
            with self.subTest(family=family):
                with self.assertRaises(Refusal):
                    Task.parse(raw)
                task, tr = convolution.prepare(source, ref, raw)
                self.assertEqual(convolution.dimensions(task), dims)
                self.assertEqual(tr.program, convolution.expected_program(task))
            for variant in ("group", "width", "output", "integer-type"):
                d = json.loads(raw)
                if variant == "group":
                    d["buffers"][1]["shape"][1] = 7
                elif variant == "width":
                    d["buffers"][0]["shape"][3] += 1
                elif variant == "output":
                    d["buffers"][2]["shape"][2] += 1
                else:
                    d["buffers"][0]["shape"][2] = float(d["buffers"][0]["shape"][2])
                with self.subTest(variant=variant), self.assertRaises(Refusal):
                    convolution.prepare(source, ref, json.dumps(d))

    def test_wrong_group_padding_and_kernel_offset_are_refused(self):
        source, ref, raw = self.sources("depthwise_conv")
        for before, after in [("groups=32", "groups=1"), ("groups=32", "groups=32,padding=1")]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                convolution.prepare(source, ref.replace(before, after), raw)
        for before, after in [
            ("(j / 5) % 5", "0"),
            ("acc = acc +", "acc = acc -"),
            ("j < 25", "j < 24"),
        ]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                convolution.prepare(source.replace(before, after), ref, raw)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_depthwise_export_recheck_and_rehashed_group_forgery(self):
        case = CASES / "depthwise_conv"
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = convolution.verify(
                case / "kernel.hip", case / "reference.py", case / "task.json", dest, lean=LEAN
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["convolution_dimensions"] = [32, 32, 16, 5, 1]
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["convolution_dimensions"] = [32, 32, 16, 5, 32]
            reference = dest / "reference.py"
            reference.write_text(reference.read_text().replace("groups=32", "groups=1"))
            report["files"]["reference.py"] = hashlib.sha256(reference.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
