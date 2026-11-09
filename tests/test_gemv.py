import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, gemv
from lark_kernels.ir import Refusal, Task

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "reproduction/reduction/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class GemvTests(unittest.TestCase):
    def sources(self):
        return tuple(
            (CASES / "hip" / f).read_text() for f in ("kernel.hip", "reference.py", "task.json")
        )

    def test_full_shape_uses_the_proved_profile_and_preserves_old_limits(self):
        source, ref, task = self.sources()
        with self.assertRaises(Refusal):
            Task.parse(task)
        parsed, tr = gemv.prepare(source, ref, task)
        self.assertEqual(parsed.buffers[0].shape, (512, 1024))
        self.assertEqual(parsed.fuel, (4102, 1, 1, 1))
        self.assertEqual(tr.program, gemv.expected_program(1024))

    def test_bad_geometry_shapes_json_types_and_fuel_are_refused(self):
        source, ref, task_source = self.sources()
        for variant in ("k", "n", "float_dimension", "float_grid", "block", "fuel"):
            task = json.loads(task_source)
            if variant == "k":
                task["buffers"][1]["shape"][0] = 1023
            elif variant == "n":
                task["buffers"][2]["shape"][0] = 511
            elif variant == "float_dimension":
                task["buffers"][2]["shape"][0] = 512.0
            elif variant == "float_grid":
                task["launch"]["grid"] = 512.0
            elif variant == "block":
                task["launch"]["block"] = 2
            else:
                task["fuel"][0] -= 1
            with self.subTest(variant=variant), self.assertRaises(Refusal):
                gemv.prepare(source, ref, json.dumps(task))

    def test_arithmetic_index_and_loop_mutations_cannot_use_the_induction_rule(self):
        source, ref, task = self.sources()
        for before, after in [
            ("acc = acc +", "acc = acc -"),
            ("a[i * 1024 + j]", "a[j]"),
            ("j < 1024", "j < 1023"),
            ("out[i]", "out[0]"),
        ]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                gemv.prepare(source.replace(before, after), ref, task)

    def test_reference_must_match_the_full_tensor_operator(self):
        source, _, task = self.sources()
        for value in [
            "(a.float() @ b.float()).half().flip([0])",
            "a.half()",
            "(a.float() + b.float()).half()",
            "(a.float() @ b.float()).half()[:1]",
        ]:
            ref = f"import torch\ndef reference(a,b):\n return {value}\n"
            with self.subTest(value=value), self.assertRaises(Refusal):
                gemv.prepare(source, ref, task)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_size_certificate_rechecks_and_forged_statement_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = CASES / "hip"
            output = Path(tmp) / "certificate"
            result = gemv.verify(
                case / "kernel.hip", case / "reference.py", case / "task.json", output, lean=LEAN
            )
            self.assertEqual(result["status"], "verified")
            certificate.check(output, lean=LEAN)
            result["matrix_shape"] = [1, 1]
            (output / "report.json").write_text(json.dumps(result))
            with self.assertRaises(Refusal):
                certificate.check(output, lean=LEAN)
            result["matrix_shape"] = [512, 1024]
            main = output / "Main.lean"
            main.write_text(
                main.read_text().replace("def spec (ops : Ops α)", "def forged (ops : Ops α)", 1)
            )
            result["files"]["Main.lean"] = hashlib.sha256(main.read_bytes()).hexdigest()
            (output / "report.json").write_text(json.dumps(result))
            with self.assertRaises(Refusal):
                certificate.check(output, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
