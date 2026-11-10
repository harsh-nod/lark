import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, normalization
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import preflight
from lark_kernels.spec import read_spec
from reproduction.normalization.make_cases import create

CASES = Path(__file__).resolve().parents[1] / "reproduction/normalization/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class NormalizationTests(unittest.TestCase):
    def sources(self, kind="layer"):
        root = CASES / kind / "hip"
        return tuple((root / f).read_text() for f in ("kernel.hip", "reference.py", "task.json"))

    def test_full_profile_refuses_bad_shapes_launch_and_fuel(self):
        source, ref, raw = self.sources()
        with self.assertRaises(Refusal):
            Task.parse(raw)
        task, _, kind = normalization.prepare(source, ref, raw)
        self.assertEqual((task.grid, kind), (16384, "layer"))
        for variant in ("shape", "bool", "fuel", "grid", "int32"):
            d = json.loads(raw)
            if variant == "shape":
                d["buffers"][1]["shape"] = [8192]
            elif variant == "bool":
                d["buffers"][0]["shape"] = [True]
            elif variant == "fuel":
                d["fuel"][0] -= 1
            elif variant == "grid":
                d["launch"]["grid"] -= 1
            else:
                d["buffers"][0]["shape"] = [2147483648]
            with self.subTest(variant=variant), self.assertRaises(Refusal):
                normalization.prepare(source, ref, json.dumps(d))

    def test_reduced_actual_machine_matches_independent_tensor_formalization(self):
        # This compares the IR interpreter with the existing tensor evaluator,
        # including sum association, max initialization, variance and FP16 casts.
        with tempfile.TemporaryDirectory() as tmp:
            for kind in normalization.KINDS:
                for n in (1, 4):
                    root = Path(tmp) / f"{kind}-{n}"
                    create(root, kind, n=n)
                    task, tr, _ = normalization.prepare(
                        *(
                            (root / f).read_text()
                            for f in ("kernel.hip", "reference.py", "task.json")
                        )
                    )
                    preflight(task, tr, read_spec((root / "reference.py").read_text(), task))

    def test_wrong_variance_seed_and_shape_dependent_references_cannot_lift(self):
        for kind, before, after in [
            ("rms", "val * val", "val + val"),
            ("layer", "(val - ctx) *", "(val + ctx) *"),
            ("softmax", "int j = 1;", "int j = 0;"),
        ]:
            source, ref, raw = self.sources(kind)
            with self.subTest(kind=kind), self.assertRaises(Refusal):
                normalization.prepare(source.replace(before, after), ref, raw)
        source, ref, raw = self.sources()
        for forged in (
            ref.replace("1e-5", "1e-4"),
            ref.replace(".half()", ".half()[:1]"),
            ref.replace("return ", "return x if x.shape[0] > 1 else "),
        ):
            with self.assertRaises(Refusal):
                normalization.prepare(source, forged, raw)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_softmax_export_recheck_and_rehashed_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            case = CASES / "softmax" / "hip"
            dest = Path(tmp) / "certificate"
            report = normalization.verify(
                case / "kernel.hip", case / "reference.py", case / "task.json", dest, lean=LEAN
            )
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["normalization_kind"] = "layer"
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["normalization_kind"] = "softmax"
            source = dest / "kernel.cu"
            source.write_text(source.read_text().replace("int j = 1;", "int j = 0;"))
            report["files"]["kernel.cu"] = hashlib.sha256(source.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
