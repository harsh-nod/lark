import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, matrix
from lark_kernels.ir import Refusal, Task
from reproduction.matrix.bundle import load_dataset

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "reproduction/matrix/cases/hip"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class MatrixTests(unittest.TestCase):
    def sources(self, family):
        return tuple(
            (CASES / family / f).read_text() for f in ("kernel.hip", "reference.py", "task.json")
        )

    def test_full_gemm_and_bmm_profiles_preserve_bounded_limits(self):
        for family, dims in [("gemm", (1, 64, 256, 512)), ("bmm", (32, 64, 256, 512))]:
            source, ref, raw = self.sources(family)
            with self.subTest(family=family):
                with self.assertRaises(Refusal):
                    Task.parse(raw)
                task, tr = matrix.prepare(source, ref, raw)
                self.assertEqual(matrix.dimensions(task), dims)
                self.assertEqual(tr.program, matrix.expected_program(task))

    def test_batch_broadcast_shape_launch_and_integer_aliases_are_refused(self):
        source, ref, raw = self.sources("bmm")
        for variant in ("broadcast", "output", "grid", "bool", "float", "fuel", "overflow"):
            task = json.loads(raw)
            if variant == "broadcast":
                task["buffers"][1]["shape"][0] = 1
            elif variant == "output":
                task["buffers"][2]["shape"][1] -= 1
            elif variant == "grid":
                task["launch"]["grid"] -= 1
            elif variant in ("bool", "float"):
                task["buffers"][0]["shape"][0] = True if variant == "bool" else 32.0
            elif variant == "fuel":
                task["fuel"][0] -= 1
            else:
                task["buffers"][0]["shape"][0] = 2147483648
            with self.subTest(variant=variant), self.assertRaises(Refusal):
                matrix.prepare(source, ref, json.dumps(task))

    def test_changed_index_and_shape_dependent_reference_cannot_use_the_rule(self):
        source, ref, raw = self.sources("bmm")
        for before, after in [
            ("i / 32768", "i / 16384"),
            ("i % 512", "i % 256"),
            ("acc = acc +", "acc = acc -"),
            ("out[i]", "out[0]"),
        ]:
            with self.subTest(after=after), self.assertRaises(Refusal):
                matrix.prepare(source.replace(before, after), ref, raw)
        for expression in [
            "(a.float() @ b.float()).half()[:1]",
            "(a.float() @ b.float()).half().transpose(0, 1)",
        ]:
            with self.subTest(expression=expression), self.assertRaises(Refusal):
                matrix.prepare(
                    source, "import torch\ndef reference(a,b):\n return " + expression, raw
                )

    def test_binary_probe_tampering_and_extent_forgery_are_refused(self):
        import struct

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = struct.pack("<ee", 0.125, -0.25)
            digest = hashlib.sha256(payload).hexdigest()
            extent = {"offset": 0, "bytes": len(payload), "sha256": digest}
            data = {
                "tensor_data_sha256": digest,
                "cases": [
                    {
                        "trials": [
                            {
                                "buffers": [{"role": "input", "packed": extent}],
                                "expected_packed": extent,
                            }
                        ]
                    }
                ],
            }
            (root / "tensors.f16").write_bytes(payload)
            (root / "cases.json").write_text(json.dumps(data))
            decoded = load_dataset(root)
            self.assertEqual(list(decoded["cases"][0]["trials"][0]["expected"]), [0.125, -0.25])
            (root / "tensors.f16").write_bytes(payload[::-1])
            with self.assertRaises(RuntimeError):
                load_dataset(root)
            (root / "tensors.f16").write_bytes(payload)
            extent["offset"] = -1
            (root / "cases.json").write_text(json.dumps(data))
            with self.assertRaises(RuntimeError):
                load_dataset(root)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_batched_certificate_and_forged_reference_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = CASES / "bmm"
            dest = Path(tmp) / "certificate"
            report = matrix.verify(
                case / "kernel.hip", case / "reference.py", case / "task.json", dest, lean=LEAN
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["matrix_dimensions"] = [1, 64, 256, 512]
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["matrix_dimensions"] = [32, 64, 256, 512]
            # The replacement has a valid one-cell matmul, but changes the
            # full tensor contract. Rehashing the manifest must not accept it.
            reference = dest / "reference.py"
            reference.write_text(
                "import torch\ndef reference(a,b):\n return (a.float() @ b.float()).half()[:1]\n"
            )
            report["files"]["reference.py"] = hashlib.sha256(reference.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
