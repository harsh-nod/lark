from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

from lark_kernels.certificate import (
    DEFAULT_PROOFS,
    check,
    default_segments,
    render,
    run_lean,
    validate_proofs,
    verify,
)
from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import Machine, preflight
from lark_kernels.spec import read_spec


ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


def load(name):
    p = EXAMPLES / name
    kernel = next(p.glob("kernel.*"))
    task = Task.read(p / "task.json")
    source = kernel.read_text()
    tr = translate(source, task)
    spec = read_spec((p / "reference.py").read_text(), task)
    return p, kernel, task, source, tr, spec


class FrontendTests(unittest.TestCase):
    def test_axiom_diagnostics_cannot_spoof_the_final_audit(self):
        names = (
            "segmentation_data",
            "segmentation",
            "race_free",
            "segment_equivalence",
            "kernel_eq_spec",
            "kernel_eq_spec_pre",
        )
        honest = "\n".join(f"'LarkCertificate.{n}' does not depend on any axioms" for n in names)
        for extra in (
            "'LarkCertificate.kernel_eq_spec' depends on axioms: [Lean.ofReduceBool]\n",
            "'LarkCertificate.kernel_eq_spec' does not depend on any axioms\n",
        ):
            with (
                self.subTest(extra=extra),
                patch(
                    "lark_kernels.certificate.subprocess.run",
                    return_value=SimpleNamespace(returncode=0, stdout=extra + honest, stderr=""),
                ),
            ):
                ok, log = run_lean(Path("."), "unused-checker", 1)
                self.assertFalse(ok)
                self.assertIn("ambiguous", log)

    def test_all_examples_preflight(self):
        for p in sorted(EXAMPLES.iterdir()):
            with self.subTest(example=p.name):
                _, _, task, source, tr, spec = load(p.name)
                self.assertEqual(tr.readback().encode(), source.encode())
                self.assertTrue(preflight(task, tr, spec).trace)

    def test_roundtrip_preserves_crlf_and_comments(self):
        _, _, task, source, _, _ = load("vector_add")
        source = "/* model input */\r\n" + source.replace("\n", "\r\n") + " // tail"
        self.assertEqual(translate(source, task).readback(), source)

    def test_arithmetic_address_register_and_loop_mutations(self):
        cases = [
            ("vector_add", "x[i] + y[i]", "x[i] - y[i]", "equivalence"),
            ("vector_add", "out[i]", "out[0]", "race"),
            ("vector_add", "x[i] + y[i]", "x[i] + x[i]", "equivalence"),
            ("matmul", "k < 2", "k < 1", "equivalence"),
            ("reverse", "__syncthreads();", "", "uninitialized"),
            ("vector_add", "x[i] + y[i]", "x[i + 1] + y[i]", "bounds"),
        ]
        for name, before, after, code in cases:
            with self.subTest(name=name, mutation=after):
                _, _, task, source, _, spec = load(name)
                tr = translate(source.replace(before, after), task)
                with self.assertRaises(Refusal) as caught:
                    preflight(task, tr, spec)
                self.assertEqual(caught.exception.code, code)

    def test_benign_same_value_writes_are_races(self):
        _, _, task, source, _, spec = load("vector_add")
        source = source.replace("out[i] = x[i] + y[i]", "out[0] = 0.0f")
        with self.assertRaisesRegex(Refusal, "threads.*conflict"):
            preflight(task, translate(source, task), spec)

    def test_block_barriers_do_not_order_distinct_blocks(self):
        _, _, task, source, _, _ = load("vector_add")
        source = source.replace(
            "out[i] = x[i] + y[i];", "out[threadIdx.x] = 0.0f; __syncthreads();"
        )
        m = Machine(task, translate(source, task)).run()
        a, b = m.race()
        self.assertNotEqual(a.thread // task.block, b.thread // task.block)

    def test_missing_output_uninitialized_local_and_divergence(self):
        cases = [
            ("out[i] = x[i] + y[i];", "", "uninitialized-output"),
            ("out[i] = x[i] + y[i];", "float v; out[i] = v;", "uninitialized"),
            ("out[i] = x[i] + y[i];", "if (threadIdx.x == 0) { __syncthreads(); }", "convergence"),
        ]
        _, _, task, source, _, spec = load("vector_add")
        for before, after, code in cases:
            with self.subTest(code=code):
                with self.assertRaises(Refusal) as caught:
                    preflight(task, translate(source.replace(before, after), task), spec)
                self.assertEqual(caught.exception.code, code)

    def test_fuel_is_an_obligation(self):
        _, _, task, _, tr, spec = load("matmul")
        task = copy.copy(task)
        object.__setattr__(task, "fuel", (2, 16, 16, 16))
        with self.assertRaisesRegex(Refusal, "fuel"):
            preflight(task, tr, spec)

    def test_integer_overflow_and_unsigned_underflow_refused(self):
        _, _, task, source, _, spec = load("vector_add")
        for expression in ("2147483647 + 1", "threadIdx.x - 1"):
            changed = source.replace("blockIdx.x * blockDim.x + threadIdx.x", expression)
            with self.assertRaisesRegex(Refusal, "int32"):
                preflight(task, translate(changed, task), spec)

    def test_unknown_constructs_refused(self):
        _, _, task, source, _, _ = load("vector_add")
        cases = [
            source + " void helper() {}",
            source.replace("float*", "double*"),
            source.replace("x[i] + y[i]", "atomicAdd(x, y[i])"),
            source.replace("int i", "unsigned int i"),
            source.replace("x[i] + y[i]", "x[i] / y[i]"),
            source.replace("threadIdx.x", "threadIdx.y"),
        ]
        for changed in cases:
            with self.subTest(source=changed):
                with self.assertRaises(Refusal):
                    translate(changed, task)

    def test_reference_never_executes_code(self):
        _, _, task, _, _, _ = load("vector_add")
        for ref in (
            "import os\ndef reference(x,y):\n return x+y\n",
            "def reference(x,y):\n return __import__('os').system('true')\n",
            "@evil\ndef reference(x,y):\n return x+y\n",
        ):
            with self.assertRaises(Refusal):
                read_spec(ref, task)

    def test_reference_namespace_and_tensor_types_are_checked(self):
        _, _, task, _, _, _ = load("vector_add")
        for body in (
            "torch = x\n return torch.relu(y)",
            "return torch.relu(1.0)",
            "return torch.view(x, 4)",
            "return torch.reshape(x, 2, 2)",
            "return 1.0",
        ):
            with self.subTest(body=body), self.assertRaises(Refusal):
                read_spec("import torch\ndef reference(x,y):\n " + body + "\n", task)

    def test_proof_escape_and_unchecked_evaluation_refused(self):
        for proof in (
            "by sorry",
            "by native_decide",
            "by admit",
            "by exact False.elim (by sorry)",
            "by rfl\naxiom h : False",
            "by run_tac pure ()",
        ):
            with self.subTest(proof=proof):
                candidate = dict(DEFAULT_PROOFS, segmentation_data=proof)
                with self.assertRaises(Refusal):
                    validate_proofs(candidate)


@unittest.skipUnless(LEAN, "set LARK_LEAN or install Lean 4.19.0 for proof integration tests")
class LeanTests(unittest.TestCase):
    def test_all_examples_certify_and_recheck(self):
        for p in sorted(EXAMPLES.iterdir()):
            with self.subTest(example=p.name), tempfile.TemporaryDirectory() as d:
                _, kernel, _, _, _, _ = load(p.name)
                out = Path(d) / "certificate"
                report = verify(kernel, p / "reference.py", p / "task.json", out, lean=LEAN)
                if report["status"] != "verified":
                    self.fail(report["axiom_audit"])
                self.assertNotIn("sorryAx", report["axiom_audit"])
                self.assertIn("kernel_eq_spec", check(out, lean=LEAN))

    def test_lean_rejects_wrong_kernel_without_python_screen(self):
        _, _, task, source, _, spec = load("vector_add")
        tr = translate(source.replace("x[i] + y[i]", "x[i] - y[i]"), task)
        proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / "Main.lean").write_text(render(task, tr, spec, proposal))
            ok, log = run_lean(p, LEAN, 60)
            self.assertFalse(ok)
            self.assertIn("error:", log)

    def test_lean_rejects_race_without_python_screen(self):
        _, _, task, source, _, spec = load("vector_add")
        tr = translate(source.replace("out[i]", "out[0]"), task)
        proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / "Main.lean").write_text(render(task, tr, spec, proposal))
            ok, log = run_lean(p, LEAN, 60)
            self.assertFalse(ok)
            self.assertIn("error:", log)

    def test_segmentation_is_not_trusted(self):
        _, _, task, _, tr, spec = load("vector_add")
        proposal = {"segments": [{"op": 0}, {"op": 2}], "proofs": dict(DEFAULT_PROOFS)}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / "Main.lean").write_text(render(task, tr, spec, proposal))
            ok, _ = run_lean(p, LEAN, 60)
            self.assertFalse(ok)

    def test_footprint_proposal_is_not_trusted(self):
        _, _, task, _, tr, spec = load("vector_add")
        proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            source = render(task, tr, spec, proposal)
            source = "\n".join(
                "def traceData : List Access := []" if line.startswith("def traceData :") else line
                for line in source.split("\n")
            )
            (p / "Main.lean").write_text(source)
            ok, log = run_lean(p, LEAN, 60)
            self.assertFalse(ok)
            self.assertIn("error:", log)

    def test_recheck_rejects_tampering_even_if_manifest_rehashed(self):
        p, kernel, _, _, _, _ = load("vector_add")
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "certificate"
            verify(kernel, p / "reference.py", p / "task.json", out, lean=LEAN)
            main = out / "Main.lean"
            main.write_text(main.read_text().replace("theorem kernel_eq_spec", "theorem unrelated"))
            from lark_kernels.certificate import digest

            report = json.loads((out / "report.json").read_text())
            report["files"]["Main.lean"] = digest(main.read_bytes())
            (out / "report.json").write_text(json.dumps(report))
            with self.assertRaisesRegex(Refusal, "fixed statement"):
                check(out, lean=LEAN)

    def test_existing_certificate_not_overwritten(self):
        p, kernel, _, _, _, _ = load("vector_add")
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(Refusal, "already exists"):
                verify(kernel, p / "reference.py", p / "task.json", Path(d), lean=LEAN)

    def test_provider_can_repair_a_failed_proposal(self):
        p, kernel, _, _, tr, _ = load("vector_add")
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            proposal = {"segments": [{"op": 0}], "proofs": dict(DEFAULT_PROOFS)}
            proposal_path = root / "initial.json"
            proposal_path.write_text(json.dumps(proposal))
            good = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
            provider = root / "repair.py"
            provider.write_text(
                "import json,sys\nr=json.load(sys.stdin)\n"
                "assert 'lean_errors' in r and 'lean_source' in r\n"
                "print(" + repr(json.dumps(good)) + ")\n"
            )
            import sys

            report = verify(
                kernel,
                p / "reference.py",
                p / "task.json",
                root / "out",
                lean=LEAN,
                proposal_path=proposal_path,
                attempts=2,
                provider=[sys.executable, str(provider)],
            )
            self.assertEqual(report["status"], "verified", report["axiom_audit"])
            self.assertEqual([x["accepted"] for x in report["attempts"]], [False, True])

    def test_lean_rejects_exhausted_fuel_without_python_screen(self):
        _, _, task, _, tr, spec = load("matmul")
        object.__setattr__(task, "fuel", (2, 16, 16, 16))
        proposal = {"segments": default_segments(tr.program), "proofs": dict(DEFAULT_PROOFS)}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / "Main.lean").write_text(render(task, tr, spec, proposal))
            ok, _ = run_lean(p, LEAN, 60)
            self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
