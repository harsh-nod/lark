import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, linear
from lark_kernels.ir import Refusal, Task

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "reproduction/linear/cases/hip"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class LinearTests(unittest.TestCase):
    def sources(self):
        return tuple((CASE / f).read_text() for f in ("kernel.hip", "reference.py", "task.json"))

    def test_full_linear_checks_third_input_and_keeps_bounded_limits(self):
        source, ref, raw = self.sources()
        with self.assertRaises(Refusal):
            Task.parse(raw)
        task, tr = linear.prepare(source, ref, raw)
        self.assertEqual(linear.dimensions(task), (1, 64, 256, 512))
        self.assertEqual(tr.program, linear.expected_program(task))
        for variant in ("bias-size", "output-role", "rank", "integer-type"):
            d = json.loads(raw)
            if variant == "bias-size":
                d["buffers"][2]["shape"] = [511]
            elif variant == "output-role":
                d["buffers"][2]["role"] = "output"
            elif variant == "rank":
                d["buffers"][2]["shape"] = [1, 512]
            else:
                d["buffers"][2]["shape"] = [512.0]
            with self.subTest(variant=variant), self.assertRaises(Refusal):
                linear.prepare(source, ref, json.dumps(d))

    def test_missing_or_wrongly_indexed_bias_is_refused(self):
        source, ref, raw = self.sources()
        for before, after in [
            ("bias[i % 512]", "bias[0]"),
            ("acc + __half2float(bias[i % 512])", "acc"),
            ("acc = acc +", "acc = acc -"),
        ]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                linear.prepare(source.replace(before, after), ref, raw)
        for before, after in [(" + bias.float()", ""), ("bias.float()", "bias.float().flip([0])")]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                linear.prepare(source, ref.replace(before, after), raw)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_linear_export_recheck_and_rehashed_bias_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = linear.verify(
                CASE / "kernel.hip", CASE / "reference.py", CASE / "task.json", dest, lean=LEAN
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            reference = dest / "reference.py"
            reference.write_text(reference.read_text().replace(" + bias.float()", ""))
            report["files"]["reference.py"] = hashlib.sha256(reference.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
