import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, rotary
from lark_kernels.ir import Refusal, Task

CASE = Path(__file__).resolve().parents[1] / "reproduction/rotary/cases/hip"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class RotaryTests(unittest.TestCase):
    def sources(self):
        return tuple((CASE / f).read_text() for f in ("kernel.hip", "reference.py", "task.json"))

    def test_full_profile_and_coefficient_shapes_preserve_bounded_limits(self):
        source, ref, raw = self.sources()
        with self.assertRaises(Refusal):
            Task.parse(raw)
        task, tr = rotary.prepare(source, ref, raw)
        self.assertEqual(task.grid, 32768)
        self.assertEqual(tr.program, rotary.expected_program())
        for variant in ("coefficient", "odd", "integer-type", "grid"):
            d = json.loads(raw)
            if variant == "coefficient":
                d["buffers"][2]["shape"][1] -= 1
            elif variant == "odd":
                d["buffers"][0]["shape"][1] = 127
            elif variant == "integer-type":
                d["buffers"][0]["shape"][0] = 256.0
            else:
                d["launch"]["grid"] -= 1
            with self.subTest(variant=variant), self.assertRaises(Refusal):
                rotary.prepare(source, ref, json.dumps(d))

    def test_wrong_parity_pairing_and_single_pair_reference_cannot_be_lifted(self):
        source, ref, raw = self.sources()
        for before, after in [
            ("t % 2 == 0", "t % 2 == 1"),
            ("(t / 2) * 2", "t"),
            (" - b *", " + b *"),
        ]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                rotary.prepare(source.replace(before, after), ref, raw)
        small = (
            "import torch\ndef reference(x,cosine,sine):\n return "
            + rotary.reference_expression(1, 2, ("x", "cosine", "sine"))
        )
        with self.assertRaises(Refusal):
            rotary.prepare(source, small, raw)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_export_recheck_and_rehashed_arithmetic_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = rotary.verify(
                CASE / "kernel.hip", CASE / "reference.py", CASE / "task.json", dest, lean=LEAN
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["rotary_shape"] = [128, 256]
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["rotary_shape"] = [256, 128]
            source = dest / "kernel.cu"
            source.write_text(source.read_text().replace(" - b *", " + b *"))
            report["files"]["kernel.cu"] = hashlib.sha256(source.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
