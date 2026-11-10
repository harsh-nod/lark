import hashlib
import json
import os
from dataclasses import replace
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import attention, certificate
from lark_kernels.ir import Node, Refusal
from lark_kernels.machine import Machine
from lark_kernels.spec import read_spec
from reproduction.attention.make_cases import create

CASES = Path(__file__).resolve().parents[1] / "reproduction/attention/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def sources(case):
    return {
        n: (case / (n.replace(".cu", ".hip") if n.endswith(".cu") else n)).read_text()
        for n in attention.SOURCE_FILES
    }


def substitute(n, inputs):
    if n.op == "input":
        return inputs(n.args[0], n.args[1])
    return Node(n.op, tuple(substitute(x, inputs) if isinstance(x, Node) else x for x in n.args))


class AttentionTests(unittest.TestCase):
    def test_composed_ir_matches_independent_tensor_reader(self):
        with tempfile.TemporaryDirectory() as tmp:
            for kv, groups, seq, dim in ((1, 1, 1, 1), (1, 1, 2, 4), (1, 2, 2, 4), (2, 2, 2, 4)):
                case = Path(tmp) / f"{kv}-{groups}-{seq}-{dim}"
                create(case, kv_heads=kv, groups=groups, seq=seq, dim=dim)
                values = sources(case)
                tasks, trs = attention.prepare(values)
                raw = [Machine(t, tr).run().outputs() for t, tr in zip(tasks, trs)]
                probabilities = [substitute(x, lambda b, i: raw[0][i]) for x in raw[1]]
                final = [
                    substitute(
                        x, lambda b, i: probabilities[i] if b == 0 else Node("input", (2, i))
                    )
                    for x in raw[2]
                ]
                reference_task = replace(
                    tasks[2],
                    buffers=(
                        tasks[0].buffers[0],
                        tasks[0].buffers[1],
                        tasks[2].buffers[1],
                        tasks[2].buffers[2],
                    ),
                )
                self.assertEqual(final, read_spec(values["reference.py"], reference_task))

    def test_source_scale_group_row_and_reference_mutations_refused(self):
        values = sources(CASES / "gqa/hip")
        for key, old, new in (
            ("score.cu", "acc / 8.0f", "acc / 4.0f"),
            ("score.cu", "/ 4)", "/ 2)"),
            ("softmax.cu", "j = 1;", "j = 0;"),
            ("softmax.cu", "(i / 128) * 128 + j", "j"),
            ("value.cu", "__float2half(acc)", "__float2half(acc + 1.0f)"),
            ("reference.py", "repeat_interleave(4,dim=0)", "repeat_interleave(2,dim=0)"),
        ):
            changed = values.copy()
            self.assertIn(old, changed[key])
            changed[key] = changed[key].replace(old, new)
            with self.subTest(key=key, new=new), self.assertRaises(Refusal):
                attention.prepare(changed)
        for key in ("score-task.json", "softmax-task.json", "value-task.json"):
            changed = values.copy()
            d = json.loads(changed[key])
            d["buffers"][0]["name"] = "unwired"
            changed[key] = json.dumps(d)
            with self.subTest(task=key), self.assertRaises(Refusal):
                attention.prepare(changed)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_gqa_export_recheck_and_rehashed_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = attention.verify(CASES / "gqa/hip", dest, lean=LEAN)
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["kernel_launches"] = 2
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["kernel_launches"] = 3
            path = dest / "softmax-task.json"
            d = json.loads(path.read_text())
            d["buffers"][0]["dtype"] = "float16"
            path.write_text(json.dumps(d))
            report["files"][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
