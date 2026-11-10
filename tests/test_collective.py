"""Full-wave shuffle source and concurrency controls; GPU execution is separate."""

from dataclasses import replace
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import collective
from lark_kernels.frontend import translate as scalar_translate
from lark_kernels.ir import Buffer, Refusal, Task
from lark_kernels.spec import read_spec

CASES = Path(__file__).resolve().parents[1] / "reproduction/shuffle/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def load(name):
    path = CASES / name
    task = Task.read(path / "task.json")
    return (
        task,
        (path / "kernel.hip").read_text(),
        read_spec((path / "reference.py").read_text(), task),
    )


class CollectiveTests(unittest.TestCase):
    def test_all_forms_match_independent_tensor_references(self):
        for case in sorted(CASES.iterdir()):
            with self.subTest(case=case.name):
                task, source, spec = load(case.name)
                source = "/* retained */\r\n" + source.replace("\n", "\r\n") + " // tail"
                tr = collective.translate(source, task)
                self.assertEqual(tr.readback().encode(), source.encode())
                machine = collective.preflight(task, tr, spec)
                self.assertEqual(len(machine.trace), 128)
                self.assertTrue(all(t.epoch == [0, 0, 0] for t in machine.threads))

    def test_in_place_shuffle_reads_the_old_wave_snapshot(self):
        task, source, spec = load("reverse")
        self.assertIn("value = __shfl(value", source)
        machine = collective.preflight(task, collective.translate(source, task), spec)
        for i, value in enumerate(machine.outputs()):
            self.assertEqual(value.args, (0, 63 - i))

    def test_shuffles_do_not_repair_memory_races(self):
        task, source, spec = load("reverse")
        task = replace(
            task, buffers=(task.buffers[0], Buffer("scratch", "scratch", (64,)), task.buffers[1])
        )
        source = source.replace("float* out)", "float* scratch, float* out)")
        source = source.replace("value = __shfl", "scratch[i] = value;\n  value = __shfl")
        source = source.replace("out[i] = value", "out[i] = scratch[63 - i]")
        tr = collective.translate(source, task)
        machine = collective.Machine(task, tr).run()
        # All stores happened in the fold, so numerical output alone passes.
        self.assertEqual(machine.outputs(), spec)
        self.assertIsNotNone(machine.race())
        with self.assertRaisesRegex(Refusal, "unordered accesses conflict"):
            collective.preflight(task, tr, spec)
        fixed = source.replace("scratch[i] = value;", "scratch[i] = value;\n  __syncthreads();")
        repaired = collective.preflight(task, collective.translate(fixed, task), spec)
        self.assertTrue(all(t.epoch == [0, 1, 0] for t in repaired.threads))

    def test_partial_participation_and_nonliteral_width_are_refused(self):
        task, source, _ = load("reverse")
        with self.assertRaisesRegex(Refusal, "full-wave64"):
            collective.translate(source, replace(task, block=32))
        changed = source.replace(
            "value = __shfl(value, 63 - i, 64);",
            "if (i < 32) { value = __shfl(value, 63 - i, 64); }",
        )
        with self.assertRaisesRegex(Refusal, "different program counters"):
            collective.Machine(task, collective.translate(changed, task)).run()
        with self.assertRaisesRegex(Refusal, "explicit literal width"):
            collective.translate(source.replace("63 - i, 64", "63 - i, i"), task)
        with self.assertRaises(Refusal):
            scalar_translate(source, task)

    def test_invalid_selector_and_uninitialized_source_are_refused(self):
        task, source, _ = load("broadcast8")
        with self.assertRaisesRegex(Refusal, "smaller than width"):
            collective.Machine(
                task, collective.translate(source.replace("value, 1, 8", "value, 8, 8"), task)
            ).run()
        with self.assertRaisesRegex(Refusal, "unavailable"):
            collective.Machine(
                task,
                collective.translate(source.replace("float value = x[i];", "float value;"), task),
            ).run()

    def test_a_shuffle_cannot_read_another_wave(self):
        task, source, _ = load("reverse")
        task = replace(
            task, block=128, buffers=tuple(replace(b, shape=(128,)) for b in task.buffers)
        )
        source = source.replace("63 - i", "63 - (i % 64)")
        machine = collective.Machine(task, collective.translate(source, task)).run()
        self.assertIsNone(machine.race())
        for i, value in enumerate(machine.outputs()):
            self.assertEqual(value.args, (0, i // 64 * 64 + 63 - i % 64))


@unittest.skipUnless(LEAN, "Lean 4.19.0 is needed")
class CollectiveLeanTests(unittest.TestCase):
    def test_whole_wave_proof_recheck_and_rehashed_statement_forgery(self):
        from lark_kernels.certificate import check, digest, write_json

        case = CASES / "reverse"
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "certificate"
            report = collective.verify(
                case / "kernel.hip", case / "reference.py", case / "task.json", out, lean=LEAN
            )
            self.assertEqual(report["status"], "verified", report["axiom_audit"])
            self.assertIn("kernel_eq_spec_pre", check(out, lean=LEAN))
            statement = out / "Main.lean"
            statement.write_text(
                statement.read_text().replace(
                    "theorem kernel_eq_spec (ops : Ops α) :\n    Correct ops layout geometry fuel program (spec ops)",
                    "theorem kernel_eq_spec (ops : Ops α) :\n    True",
                )
            )
            report["files"]["Main.lean"] = digest(statement.read_bytes())
            write_json(out / "report.json", report)
            with self.assertRaisesRegex(Refusal, "source-bound collective statement differs"):
                check(out, lean=LEAN)

    def test_wrong_shuffle_rejected_by_lean_without_preflight(self):
        from lark_kernels import certificate

        task, source, spec = load("broadcast8")
        tr = collective.translate(source.replace("value, 1, 8", "value, 2, 8"), task)
        machine = collective.Machine(task, tr).run()
        proposal = {
            "segments": certificate.default_segments(tr.program),
            "proofs": collective.default_proofs(task, tr, spec, machine.trace),
        }
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "Main.lean").write_text(collective.render(task, tr, spec, proposal))
            accepted, log = certificate.run_lean(out, LEAN, 90)
            self.assertFalse(accepted)
            self.assertIn("error:", log)
            self.assertNotIn("Lean timed out", log)


if __name__ == "__main__":
    unittest.main()
