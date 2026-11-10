import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import certificate, feedforward
from lark_kernels.ir import Buffer, Node, Refusal
from lark_kernels.machine import Machine
from lark_kernels.spec import read_spec
from reproduction.feedforward.make_cases import create

CASES = Path(__file__).resolve().parents[1] / "reproduction/feedforward/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def sources(case):
    return tuple(
        (case / f).read_text()
        for f in ("up.hip", "down.hip", "reference.py", "up-task.json", "down-task.json")
    )


class FeedForwardTests(unittest.TestCase):
    def test_full_pipeline_refuses_wrong_wire_alias_and_shape(self):
        values = list(sources(CASES / "hip"))
        tasks, _ = feedforward.prepare(*values)
        self.assertEqual(feedforward.dimensions(tasks), (64, 256, 1024, 256))
        for mutation in ("name", "shape", "alias", "language"):
            changed = values.copy()
            d = json.loads(changed[4])
            if mutation == "name":
                d["buffers"][0]["name"] = "unwired"
            elif mutation == "shape":
                d["buffers"][0]["shape"] = [64, 512]
            elif mutation == "alias":
                d["buffers"][2]["name"] = "x"
            else:
                d["language"] = "cuda"
            changed[4] = json.dumps(d)
            with self.subTest(mutation=mutation), self.assertRaises(Refusal):
                feedforward.prepare(*changed)

    def test_reduced_composition_matches_independent_tensor_formalization(self):
        from dataclasses import replace

        with tempfile.TemporaryDirectory() as tmp:
            for size in (1, 2):
                case = Path(tmp) / str(size)
                create(case, m=size, k=size, h=size, n=size)
                values = sources(case)
                tasks, trs = feedforward.prepare(*values)
                hidden = Machine(tasks[0], trs[0]).run().outputs()
                actual = Machine(tasks[1], trs[1]).run().outputs()

                def connect(n):
                    if n.op == "input":
                        b, i = n.args
                        return hidden[i] if b == 0 else Node("input", (2, i))
                    return Node(
                        n.op, tuple(connect(x) if isinstance(x, Node) else x for x in n.args)
                    )

                reference_task = replace(
                    tasks[1],
                    buffers=(
                        tasks[0].buffers[0],
                        tasks[0].buffers[1],
                        tasks[1].buffers[1],
                        Buffer("out", "output", (size, size), "float16"),
                    ),
                )
                self.assertEqual([connect(x) for x in actual], read_spec(values[2], reference_task))

    def test_missing_relu_and_wrong_rounding_boundary_are_refused(self):
        values = list(sources(CASES / "hip"))
        changed = values.copy()
        changed[0] = changed[0].replace("fmaxf(acc, 0.0f)", "acc")
        with self.assertRaises(Refusal):
            feedforward.prepare(*changed)
        for old, new in (
            (".relu().half().float()", ".half().float().relu()"),
            (".relu()", ".silu()"),
            (".half()", ".half()[:1]"),
        ):
            changed = values.copy()
            changed[2] = changed[2].replace(old, new)
            with self.subTest(new=new), self.assertRaises(Refusal):
                feedforward.prepare(*changed)

    @unittest.skipUnless(LEAN, "Lean is needed")
    def test_full_export_recheck_and_rehashed_wire_forgery(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "certificate"
            report = feedforward.verify(CASES / "hip", dest, lean=LEAN)
            self.assertEqual(report["status"], "verified")
            certificate.check(dest, lean=LEAN)
            report["ffn_dimensions"] = [64, 256, 512, 256]
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)
            report["ffn_dimensions"] = [64, 256, 1024, 256]
            task = dest / "down-task.json"
            d = json.loads(task.read_text())
            d["buffers"][0]["name"] = "unwired"
            task.write_text(json.dumps(d))
            report["files"][task.name] = hashlib.sha256(task.read_bytes()).hexdigest()
            (dest / "report.json").write_text(json.dumps(report))
            with self.assertRaises(Refusal):
                certificate.check(dest, lean=LEAN)


if __name__ == "__main__":
    unittest.main()
