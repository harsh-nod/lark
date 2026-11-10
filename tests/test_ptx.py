"""PTX translation controls, including failures checked directly by Lean."""

from dataclasses import replace
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
from lark_kernels.machine import Machine, preflight
from lark_kernels.spec import read_spec

CASES = Path(__file__).resolve().parents[1] / "reproduction/ptx/cases"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def load(name):
    root = CASES / name
    task = Task.read(root / "task.json")
    return (
        task,
        (root / "kernel.ptx").read_text(),
        read_spec((root / "reference.py").read_text(), task),
    )


class PTXTests(unittest.TestCase):
    def test_independent_references_and_lossless_roundtrip(self):
        for p in sorted(CASES.iterdir()):
            with self.subTest(case=p.name):
                task, source, spec = load(p.name)
                source = "/* preserved */\r\n" + source.replace("\n", "\r\n") + " // tail"
                tr = translate(source, task)
                self.assertEqual(tr.readback(), source)
                self.assertEqual(preflight(task, tr, spec).outputs(), spec)
                self.assertEqual(task.warp, 32)

    def test_bounds_guard_and_negated_predicate_agree(self):
        task, source, spec = load("vector_add")
        alternative = source.replace("setp.ge.u32", "setp.lt.u32").replace("@%p0 bra", "@!%p0 bra")
        original = preflight(task, translate(source, task), spec)
        negated = preflight(task, translate(alternative, task), spec)
        self.assertEqual(original.trace, negated.trace)
        self.assertEqual(len(original.trace), 9)  # Three active lanes; padding does no memory work.

    def test_arithmetic_register_and_byte_address_mutations(self):
        task, source, spec = load("vector_add")
        changes = [
            ("add.rn.f32", "sub.rn.f32", "equivalence"),
            ("%f0, %f1", "%f0, %f0", "equivalence"),
            ("%rd2, %rd3", "%rd2, 0", "race"),
            ("%r4, 4", "%r4, 2", "fuel"),
            ("setp.ge.u32 %p0, %r4, 3", "setp.ge.u32 %p0, %r4, 4", "bounds"),
        ]
        for before, after, code in changes:
            with self.subTest(change=after):
                self.assertIn(before, source)
                with self.assertRaises(Refusal) as caught:
                    preflight(task, translate(source.replace(before, after), task), spec)
                self.assertEqual(caught.exception.code, code)

    def test_skipped_pointer_and_predicate_initialization_is_preserved(self):
        task, source, _ = load("vector_add")
        changes = [
            (
                "ld.param.u64 %rd0, [x];",
                "bra skip; ld.param.u64 %rd0, [x]; skip:",
            ),
            (
                "setp.ge.u32 %p0, %r4, 3;",
                "bra skip; setp.ge.u32 %p0, %r4, 3; skip:",
            ),
        ]
        for before, after in changes:
            with self.subTest(change=after), self.assertRaisesRegex(Refusal, "uninitialized"):
                Machine(task, translate(source.replace(before, after), task)).run()

    def test_unsupported_forms_cannot_be_silently_ignored(self):
        task, source, _ = load("vector_add")
        changes = [
            (".version 8.0", ".version 9.0"),
            (".target sm_80", ".target sm_90"),
            (".address_size 64", ".address_size 32"),
            ("add.rn.f32", "add.rn.ftz.f32"),
            ("ld.global.f32", "ld.global.v2.f32"),
            ("add.rn.f32", "fma.rn.f32"),
            ("@%p0 bra done;", "@%p0 st.global.f32 [%rd2], 0f00000000;"),
            ("@%p0 bra done;", "again: @%p0 bra again;"),
            ("@%p0 bra done;", "@%p0 bra missing;"),
            ("add.u32 %r4, %r3, %r0;", "add.u32 %r3, %r3, %r0;"),
            ("mul.wide.u32 %rd3, %r4, 4;", "mul.wide.u32 %r5, %r4, 4;"),
            ("mul.lo.u32 %r3, %r1, %r2;", "mul.lo.u32 %r3, %rd0, %r2;"),
            ("mul.lo.u32 %r3, %r1, %r2;", "mul.lo.u32 %r3, %tid.x, %r2;"),
            ("ret;", "ret; mov.u32 %r5, 1;"),
            ("ret;", "ret; } .entry other() { ret;"),
        ]
        for before, after in changes:
            with self.subTest(change=after), self.assertRaises(Refusal):
                translate(source.replace(before, after), task)

    def test_runtime_integer_overflow_and_nonfinite_literals_are_refused(self):
        task, source, _ = load("relu")
        changed = source.replace("%r0, 4", "1073741824, 4")
        with self.assertRaisesRegex(Refusal, "integer-overflow"):
            Machine(task, translate(changed, task)).run()
        for value in ("0f7f800000", "0f7fc00000"):
            with self.subTest(value=value), self.assertRaisesRegex(Refusal, "ptx-literal"):
                translate(source.replace("0f00000000", value), task)
        data = json.loads((CASES / "relu/task.json").read_text())
        data["launch"]["warp"] = 64
        with self.assertRaisesRegex(Refusal, "warp=32"):
            Task.parse(json.dumps(data))


@unittest.skipUnless(LEAN, "Lean 4.19.0 is needed")
class PTXLeanTests(unittest.TestCase):
    def test_all_ptx_certificates_export_and_recheck(self):
        for case in sorted(CASES.iterdir()):
            with self.subTest(case=case.name), tempfile.TemporaryDirectory() as tmp:
                output = Path(tmp) / "certificate"
                report = verify(
                    case / "kernel.ptx",
                    case / "reference.py",
                    case / "task.json",
                    output,
                    lean=LEAN,
                )
                self.assertEqual(report["status"], "verified", report["axiom_audit"])
                self.assertIn("kernel.ptx", report["files"])
                self.assertNotIn("kernel.cu", report["files"])
                self.assertIn("kernel_eq_spec", check(output, lean=LEAN))
                (output / "kernel.ptx").write_text(
                    "// changed\n" + (output / "kernel.ptx").read_text()
                )
                with self.assertRaisesRegex(Refusal, "file changed"):
                    check(output, lean=LEAN)

    def test_lean_rejects_mutants_without_python_preflight(self):
        task, source, spec = load("vector_add")
        changes = [
            ("add.rn.f32", "sub.rn.f32"),
            ("%rd2, %rd3", "%rd2, 0"),
            ("%r4, 4", "%r4, 2"),
            (
                "setp.ge.u32 %p0, %r4, 3;",
                "bra skip; setp.ge.u32 %p0, %r4, 3; skip:",
            ),
        ]
        # The honest lowered program fits this bound; the alignment mutant
        # stays at its failed guard and cannot produce a final state.
        task = replace(task, fuel=(32, 16, 16, 16))
        for before, after in changes:
            with self.subTest(change=after), tempfile.TemporaryDirectory() as tmp:
                tr = translate(source.replace(before, after), task)
                proposal = {
                    "segments": default_segments(tr.program),
                    "proofs": dict(DEFAULT_PROOFS),
                }
                dest = Path(tmp)
                (dest / "Main.lean").write_text(render(task, tr, spec, proposal))
                accepted, log = run_lean(dest, LEAN, 60)
                self.assertFalse(accepted)
                self.assertIn("error:", log)
                self.assertNotIn("Lean timed out", log)


if __name__ == "__main__":
    unittest.main()
