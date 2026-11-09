import hashlib
import copy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels.certificate import (
    DEFAULT_PROOFS,
    check,
    default_segments,
    render,
    run_lean,
    verify,
)
from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import preflight
from lark_kernels.spec import read_spec
from reproduction.nonlinear.gpu_bundle import wrapper_source, validate_bundle

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "reproduction/nonlinear/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class NonlinearTests(unittest.TestCase):
    def test_half_view_preserves_the_conversion_boundary(self):
        task = Task.read(CASES / "float32/silu/task.json")
        spec = read_spec("def reference(x):\n return x.half().flip([0]).float()\n", task)
        for i, value in enumerate(spec):
            self.assertEqual(value.op, "un")
            self.assertEqual(value.args[0], "fromHalf")
            self.assertEqual(value.args[1].args[0], "toHalf")
            self.assertEqual(value.args[1].args[1].args, (0, 3 - i))

    def test_all_extended_cases_match_the_independent_spec(self):
        cases = sorted(CASES.glob("*/*"))
        self.assertEqual(len(cases), 22)
        for p in cases:
            with self.subTest(case=str(p.relative_to(CASES))):
                task = Task.read(p / "task.json")
                preflight(
                    task,
                    translate((p / "kernel.hip").read_text(), task),
                    read_spec((p / "reference.py").read_text(), task),
                )

    def test_half_operations_require_explicit_conversions(self):
        p = CASES / "float16/silu"
        task = Task.read(p / "task.json")
        source = (p / "kernel.hip").read_text()
        for before, after in [
            ("__half2float(x[i])", "x[i]"),
            ("__half* out", "float* out"),
            ("__float2half(", "__half2float("),
        ]:
            with self.subTest(change=after), self.assertRaises(Refusal):
                translate(source.replace(before, after, 1), task)
        with self.assertRaises(Refusal):
            read_spec(
                "import torch\ndef reference(x):\n return torch.nn.functional.silu(x).half()\n",
                task,
            )

    def test_unknown_functions_options_and_dtype_changes_are_refused(self):
        task = Task.read(CASES / "float32/gelu/task.json")
        for expression in [
            "torch.nn.functional.gelu(x)",
            'torch.nn.functional.gelu(x, approximate="none")',
            "torch.nn.functional.exp(x)",
            "torch.silu(x)",
            'torch.gelu(x, approximate="tanh")',
            "torch.mean(x, dim=0, keepdim=1)",
            "torch.softmax(x,dim=4)",
            "x.half()",
        ]:
            with self.subTest(expression=expression), self.assertRaises(Refusal):
                read_spec("import torch\ndef reference(x):\n return " + expression + "\n", task)

    def test_model_choice_is_derived_from_program_and_spec(self):
        for dtype in ("float32", "float16"):
            p = CASES / dtype / "softmax"
            task = Task.read(p / "task.json")
            tr = translate((p / "kernel.hip").read_text(), task)
            lean = render(
                task,
                tr,
                read_spec((p / "reference.py").read_text(), task),
                {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)},
            )
            self.assertIn("open LarkNonlinear", lean)
            self.assertIn("theorem kernel_eq_spec", lean)
            self.assertNotIn("sorry", lean)

    def test_original_machine_is_still_pinned(self):
        self.assertEqual(
            hashlib.sha256((ROOT / "lean/Lark/Model.lean").read_bytes()).hexdigest(),
            "20aeff0bb4da384fd55a636a85ccd24b742ce890629300cb2fc8cc524e02b12e",
        )


class DeviceBundleTests(unittest.TestCase):
    def fixture(self):
        p = CASES / "float16/silu"
        task = json.loads((p / "task.json").read_text())
        row = {"key": "float16/silu", "dtype": "float16", "trials": [], "rtol": 0.01, "atol": 0.01}
        cert = {"status": "verified"}
        for name, file in [
            ("source", "kernel.hip"),
            ("reference", "reference.py"),
            ("task", "task.json"),
        ]:
            row[name + "_text"] = (p / file).read_text()
            row[name + "_sha256"] = hashlib.sha256((p / file).read_bytes()).hexdigest()
            cert[name + "_sha256"] = row[name + "_sha256"]
        for trial in range(10):
            row["trials"].append(
                {
                    "trial": trial,
                    "buffers": [
                        {
                            "role": b["role"],
                            "dtype": b["dtype"],
                            "size": 4,
                            "values": [0.0] * 4 if b["role"] == "input" else None,
                        }
                        for b in task["buffers"]
                    ],
                    "expected": [0.0] * 4,
                }
            )
        wrapper = wrapper_source([row])
        data = {"cases": [row], "wrapper_sha256": hashlib.sha256(wrapper.encode()).hexdigest()}
        return data, {"float16/silu": cert}, wrapper

    def test_wrapper_is_reconstructed_from_certified_bytes(self):
        data, index, wrapper = self.fixture()
        validate_bundle(data, index, wrapper)
        changed = wrapper + "\n// changed wrapper\n"
        data["wrapper_sha256"] = hashlib.sha256(changed.encode()).hexdigest()
        with self.assertRaisesRegex(RuntimeError, "Wrapper differs"):
            validate_bundle(data, index, changed)
        data, index, wrapper = self.fixture()
        data["cases"][0]["source_text"] += "\n"
        with self.assertRaisesRegex(RuntimeError, "binding mismatch"):
            validate_bundle(data, index, wrapper)

    def test_allocations_and_comparison_protocol_are_fixed(self):
        original, index, wrapper = self.fixture()
        for field in ("size", "nan", "tolerance", "trials"):
            data = copy.deepcopy(original)
            if field == "size":
                data["cases"][0]["trials"][0]["buffers"][0]["size"] = 1
            elif field == "nan":
                data["cases"][0]["trials"][0]["expected"][0] = float("nan")
            elif field == "tolerance":
                data["cases"][0]["atol"] = 1e10
            else:
                data["cases"][0]["trials"].pop()
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                validate_bundle(data, index, wrapper)


@unittest.skipUnless(LEAN, "Lean 4.19.0 is required")
class NonlinearLeanTests(unittest.TestCase):
    def test_half_silu_certificate_and_tamper_check(self):
        p = CASES / "float16/silu"
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            result = verify(p / "kernel.hip", p / "reference.py", p / "task.json", dest, lean=LEAN)
            self.assertEqual(result["status"], "verified")
            self.assertEqual(result["model_profile"], "nonlinear-v2")
            check(dest, lean=LEAN)
            result["model_sha256"] = (
                "20aeff0bb4da384fd55a636a85ccd24b742ce890629300cb2fc8cc524e02b12e"
            )
            (dest / "report.json").write_text(json.dumps(result))
            with self.assertRaisesRegex(Refusal, "model version"):
                check(dest, lean=LEAN)

    def test_nonlinear_mutant_reaches_and_fails_lean(self):
        p = CASES / "float32/softmax"
        task = Task.read(p / "task.json")
        changed = (p / "kernel.hip").read_text().replace("weights[i] / total", "weights[0] / total")
        tr = translate(changed, task)
        spec = read_spec((p / "reference.py").read_text(), task)
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp)
            (dest / "Main.lean").write_text(
                render(
                    task,
                    tr,
                    spec,
                    {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)},
                )
            )
            ok, log = run_lean(dest, LEAN, 120)
            self.assertFalse(ok)
            self.assertIn("error:", log)
            self.assertNotIn("Lean timed out", log)


if __name__ == "__main__":
    unittest.main()
