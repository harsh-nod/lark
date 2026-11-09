import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, pointwise
from lark_kernels.ir import Refusal, Task

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "reproduction/pointwise/cases/hip/relu"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class PointwiseTests(unittest.TestCase):
    def sources(self):
        return tuple((CASE / p).read_text() for p in ("kernel.hip", "reference.py", "task.json"))

    def test_full_length_profile_keeps_the_bounded_verifier_bounded(self):
        source, ref, task = self.sources()
        with self.assertRaises(Refusal):
            Task.parse(task)
        parsed, tr, body, spec = pointwise.prepare(source, ref, task)
        self.assertEqual(parsed.grid, 16384)
        self.assertEqual(parsed.buffers[0].size, 16384)
        self.assertEqual(body, spec)
        self.assertEqual(len(tr.program), 4)

    def test_rejects_unproved_launch_layout_and_source_changes(self):
        source, ref, task_source = self.sources()
        for field, value in [("block", 2), ("grid", 10), ("warp", 32)]:
            task = json.loads(task_source)
            task["launch"][field] = value
            with self.subTest(field=field), self.assertRaises(Refusal):
                pointwise.prepare(source, ref, json.dumps(task))
        for old, new in [("blockIdx.x", "threadIdx.x"), ("out[i]", "out[0]"), ("x[i]", "x[i + 1]")]:
            with self.subTest(new=new), self.assertRaises(Refusal):
                pointwise.prepare(source.replace(old, new), ref, task_source)
        for target in ("output_shape", "grid", "fuel"):
            task = json.loads(task_source)
            if target == "output_shape":
                task["buffers"][1]["shape"] = [16384.0]
            elif target == "grid":
                task["launch"]["grid"] = 16384.0
            else:
                task["fuel"][1] = True
            with self.subTest(target=target), self.assertRaises(Refusal):
                pointwise.prepare(source, ref, json.dumps(task))

    def test_shape_dependent_reference_cannot_be_lifted_from_a_single_cell(self):
        source, _, task = self.sources()
        # Each expression is identity on a length-one tensor. They must still be
        # refused: the pointwise induction rule cannot justify these programs.
        for expression in ["x.flip([0])", "x.reshape(1)", "x[:1]", "x.sum()", "x.softmax(0)"]:
            ref = f"import torch\ndef reference(x):\n return {expression}\n"
            with self.subTest(expression=expression), self.assertRaises(Refusal):
                pointwise.prepare(source, ref, task)

    def test_scalar_disagreement_is_left_to_lean(self):
        source, ref, task = self.sources()
        _, _, body, spec = pointwise.prepare(
            source.replace("fmaxf(v, 0.0f)", "v + 0.0f"), ref, task
        )
        self.assertNotEqual(body, spec)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_length_certificate_rechecks_and_statement_tampering_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / "certificate"
            report = pointwise.verify(
                CASE / "kernel.hip",
                CASE / "reference.py",
                CASE / "task.json",
                destination,
                lean=LEAN,
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(destination, lean=LEAN)
            main = destination / "Main.lean"
            main.write_text(
                main.read_text().replace(
                    "def referenceBody : Scalar :=", "def unrelatedBody : Scalar :=", 1
                )
            )
            report["files"]["Main.lean"] = hashlib.sha256(main.read_bytes()).hexdigest()
            (destination / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(destination, lean=LEAN)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_wrong_full_length_scalar_program_receives_no_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, _, _ = self.sources()
            kernel = Path(tmp) / "wrong.hip"
            kernel.write_text(source.replace("fmaxf(v, 0.0f)", "v + 0.0f"))
            report = pointwise.verify(
                kernel,
                CASE / "reference.py",
                CASE / "task.json",
                Path(tmp) / "certificate",
                lean=LEAN,
            )
            self.assertEqual(report["status"], "unproved")


if __name__ == "__main__":
    unittest.main()
