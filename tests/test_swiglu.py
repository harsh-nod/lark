import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, swiglu
from lark_kernels.ir import Node, Refusal
from lark_kernels.machine import Machine
from lark_kernels.spec import read_spec
from reproduction.swiglu.make_cases import create

CASES = Path(__file__).resolve().parents[1] / "reproduction/swiglu/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def sources(case):
    return {
        name: (case / (name.replace(".cu", ".hip") if name.endswith(".cu") else name)).read_text()
        for name in swiglu.SOURCE_FILES
    }


def substitute(n, inputs):
    if n.op == "input":
        return inputs(n.args[0], n.args[1])
    return Node(n.op, tuple(substitute(x, inputs) if isinstance(x, Node) else x for x in n.args))


class SwiGLUTests(unittest.TestCase):
    def test_full_pipeline_requires_fp32_projections_and_exact_wiring(self):
        values = sources(CASES / "hip")
        tasks, _ = swiglu.prepare(values)
        self.assertEqual(swiglu.dimensions(tasks), (64, 256, 1024, 256))
        self.assertEqual(tasks[0].buffers[2].dtype, "float32")
        for key, mutation in (
            ("gate-task.json", "dtype"),
            ("combine-task.json", "wire"),
            ("up-task.json", "shared-x"),
            ("down-task.json", "fuel"),
        ):
            changed = values.copy()
            d = json.loads(changed[key])
            if mutation == "dtype":
                d["buffers"][2]["dtype"] = "float16"
            elif mutation == "wire":
                d["buffers"][0]["name"] = "unwired"
            elif mutation == "shared-x":
                d["buffers"][0]["name"] = "other_x"
            else:
                d["fuel"][0] -= 1
            changed[key] = json.dumps(d)
            with self.subTest(mutation=mutation), self.assertRaises(Refusal):
                swiglu.prepare(changed)

    def test_reduced_four_stage_ir_matches_independent_tensor_reader(self):
        from dataclasses import replace

        with tempfile.TemporaryDirectory() as tmp:
            for size in (1, 2):
                case = Path(tmp) / str(size)
                create(case, m=size, k=size, h=size, n=size)
                values = sources(case)
                tasks, trs = swiglu.prepare(values)
                raw = [Machine(t, tr).run().outputs() for t, tr in zip(tasks, trs)]
                gate = raw[0]
                up = [
                    substitute(x, lambda b, i: Node("input", (0 if b == 0 else 2, i)))
                    for x in raw[1]
                ]
                hidden = [substitute(x, lambda b, i: gate[i] if b == 0 else up[i]) for x in raw[2]]
                final = [
                    substitute(x, lambda b, i: hidden[i] if b == 0 else Node("input", (3, i)))
                    for x in raw[3]
                ]
                reference_task = replace(
                    tasks[3],
                    buffers=(
                        tasks[0].buffers[0],
                        tasks[0].buffers[1],
                        tasks[1].buffers[1],
                        tasks[3].buffers[1],
                        tasks[3].buffers[2],
                    ),
                )
                # Checks multiplication-by-reciprocal SiLU, FP32 projection
                # identity stores and the single FP16 intermediate boundary.
                self.assertEqual(final, read_spec(values["reference.py"], reference_task))

    def test_early_half_wrong_silu_and_reordered_reference_are_refused(self):
        values = sources(CASES / "hip")
        for key, old, new in (
            ("gate.cu", "gate[i] = acc;", "gate[i] = __half2float(__float2half(acc));"),
            ("combine.cu", "expf(0.0f - a)", "expf(a)"),
            ("combine.cu", "a * (1.0f / (1.0f + expf(0.0f - a)))", "a / (1.0f + expf(0.0f - a))"),
            ("reference.py", ".half().float()", ".half().float().relu()"),
        ):
            changed = values.copy()
            self.assertIn(old, changed[key])
            changed[key] = changed[key].replace(old, new)
            with self.subTest(key=key, new=new), self.assertRaises(Refusal):
                swiglu.prepare(changed)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_export_recheck_and_rehashed_dtype_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = swiglu.verify(CASES / "hip", dest, lean=LEAN)
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["kernel_launches"] = 2
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["kernel_launches"] = 4
            path = dest / "gate-task.json"
            d = json.loads(path.read_text())
            d["buffers"][2]["dtype"] = "float16"
            path.write_text(json.dumps(d))
            report["files"][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
