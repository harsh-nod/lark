"""MFMA frontend and concurrency controls; Lean and hardware validation are separate."""

from dataclasses import replace
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
import unittest

from lark_kernels import mfma
from lark_kernels.ir import Refusal, Task
from lark_kernels.spec import read_spec

CASE = Path(__file__).resolve().parents[1] / "reproduction/mfma/cases/gemm16"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def load():
    task = Task.read(CASE / "task.json")
    source, reference = (CASE / "kernel.hip").read_text(), (CASE / "reference.py").read_text()
    return task, source, reference


class MFMATests(unittest.TestCase):
    def test_row_major_tile_matches_independent_matrix_reference(self):
        task, source, ref = load()
        source = "/* retained */\r\n" + source.replace("\n", "\r\n") + " // tail"
        tr = mfma.translate(source, task)
        self.assertEqual(tr.readback().encode(), source.encode())
        machine = mfma.preflight(task, tr, read_spec(ref, task))
        self.assertEqual(len(tr.program), 19)
        self.assertEqual(tr.program[13].args, (8, 0, 4, 8))
        self.assertEqual(len(machine.trace), 1024)
        self.assertTrue(all(t.epoch == [0, 0, 0] for t in machine.threads))

    def test_input_layout_and_accumulator_mutations_are_detected(self):
        task, source, ref = load()
        for before, after in [
            ("(lane % 16) * 16", "(lane % 16) * 8"),
            ("H4 right = {b[", "H4 right = {a["),
            ("F4 acc = {c[", "F4 acc = {out["),
        ]:
            with self.subTest(change=after), self.assertRaises(Refusal):
                mfma.preflight(
                    task, mfma.translate(source.replace(before, after), task), read_spec(ref, task)
                )

    def test_uninitialized_accumulator_and_divergent_participation_are_refused(self):
        task, source, _ = load()
        start, end = source.index("  F4 acc ="), source.index(";", source.index("  F4 acc ="))
        changed = source[:start] + "  F4 acc" + source[end:]
        with self.assertRaisesRegex(Refusal, "accumulator register is unavailable"):
            mfma.Machine(task, mfma.translate(changed, task)).run()
        changed = source.replace("  acc = __builtin", "  if (lane < 32) { acc = __builtin").replace(
            "acc, 0, 0, 0);", "acc, 0, 0, 0); }"
        )
        with self.assertRaisesRegex(Refusal, "different program counters"):
            mfma.Machine(task, mfma.translate(changed, task)).run()

    def test_unsupported_types_components_and_modifiers_fail_closed(self):
        task, source, _ = load()
        for before, after in [
            ("acc, 0, 0, 0)", "acc, 0, 1, 0)"),
            ("acc[0]", "acc[4]"),
            ("ext_vector_type(4)", "ext_vector_type(8)"),
            ("H4 left =", "F4 left ="),
            ("left, right, acc", "acc, right, acc"),
        ]:
            with self.subTest(change=after), self.assertRaises(Refusal):
                mfma.translate(source.replace(before, after), task)
        with self.assertRaisesRegex(Refusal, "full-wave64"):
            mfma.translate(source, replace(task, block=32))

    def test_distinct_waves_use_their_own_operand_registers(self):
        task, source, ref = load()
        task = replace(
            task, block=128, buffers=tuple(replace(b, shape=(2, 16, 16)) for b in task.buffers)
        )
        source = source.replace(
            "int lane = threadIdx.x;",
            "int lane = threadIdx.x % 64;\n  int wave = threadIdx.x / 64;",
        )
        for name in ("a", "b", "c", "out"):
            source = re.sub(r"\b" + name + r"\[", name + "[wave * 256 + ", source)
        machine = mfma.preflight(task, mfma.translate(source, task), read_spec(ref, task))
        self.assertEqual(len(machine.outputs()), 512)
        self.assertEqual(len(machine.trace), 2048)


@unittest.skipUnless(LEAN, "Lean 4.19.0 is needed")
class MFMALeanTests(unittest.TestCase):
    def test_export_recheck_and_fully_rehashed_last_output_forgery(self):
        from lark_kernels import certificate

        task, source, ref = load()
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "certificate"
            report = mfma.verify(
                CASE / "kernel.hip", CASE / "reference.py", CASE / "task.json", out, lean=LEAN
            )
            self.assertEqual(report["status"], "verified", report["axiom_audit"])
            self.assertIn("kernel_eq_spec_pre", certificate.check(out, lean=LEAN))
            # Change only C[15,15] to C[15,14] in the independent reference.
            last = (
                "torch.stack(("
                + ", ".join(f"c.select(0, 15).select(0, {min(i, 14)})" for i in range(16))
                + "), dim=0)"
            )
            replacement = (
                "torch.stack(("
                + ", ".join([f"c.select(0, {i})" for i in range(15)] + [last])
                + "), dim=0)"
            )
            changed = ref.replace(" + c", " + " + replacement)
            before, after = read_spec(ref, task), read_spec(changed, task)
            self.assertEqual(before[:-1], after[:-1])
            self.assertNotEqual(before[-1], after[-1])
            (out / "reference.py").write_text(changed)
            proposal = json.loads((out / "proposal.json").read_text())
            (out / "Main.lean").write_text(
                mfma.render(task, mfma.translate(source, task), after, proposal)
            )
            for name in ("Main.lean", "reference.py"):
                report["files"][name] = certificate.digest((out / name).read_bytes())
            certificate.write_json(out / "report.json", report)
            with self.assertRaises(Refusal) as caught:
                certificate.check(out, lean=LEAN)
            self.assertEqual(caught.exception.code, "proof")
            self.assertIn("error:", str(caught.exception))
            self.assertNotIn("Lean timed out", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
