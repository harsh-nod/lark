import json
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import silu
from lark_kernels.certificate import check, digest, lean_binary, run_lean
from lark_kernels.ir import Node, Refusal

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "reproduction/production_activation/cases/silu_and_mul"


def sources(rows, width, language="hip"):
    source = (BASE / "kernel.cu").read_text().replace("5", str(width))
    reference = (
        (BASE / "reference.py")
        .read_text()
        .replace("reshape(2, 2, 5)", f"reshape({rows}, 2, {width})")
    )
    task = json.loads((BASE / "task.json").read_text())
    task["language"] = language
    task["buffers"][0]["shape"] = [rows, width]
    task["buffers"][1]["shape"] = [rows, 2 * width]
    task["launch"] = {
        "grid": rows,
        "block": min(width, 1024),
        "warp": 64 if language == "hip" else 32,
    }
    task["fuel"] = [7 * width + 4, 1, 1, 1]
    return source, reference, task


def write_case(path, source, reference, task):
    path.mkdir()
    (path / "kernel.cu").write_bytes(source.encode())
    (path / "reference.py").write_text(reference)
    (path / "task.json").write_text(json.dumps(task, indent=2) + "\n")


class SiluTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.binary = lean_binary()
        cls.temp = tempfile.TemporaryDirectory(prefix="lark-silu-test-")
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        source, reference, task = sources(64, 4097)
        source = source.replace("\n", "\r\n")
        case = cls.root / "case"
        write_case(case, source, reference, task)
        cls.certificate = cls.root / "certificate"
        cls.report = silu.verify(
            case / "kernel.cu",
            case / "reference.py",
            case / "task.json",
            cls.certificate,
            lean=cls.binary,
            timeout=150,
        )

    def test_large_launch_and_lossless_recheck(self):
        self.assertEqual(self.report["status"], "verified")
        self.assertEqual(self.report["output_elements"], 262208)
        source = (self.certificate / "kernel.cu").read_bytes().decode()
        self.assertIn("\r\n", source)
        task, tr, _ = silu.prepare(
            source,
            (self.certificate / "reference.py").read_text(),
            (self.certificate / "task.json").read_text(),
        )
        self.assertEqual(tr.readback(), source)
        self.assertEqual((task.grid, task.block, task.warp), (64, 1024, 64))
        check(self.certificate, lean=self.binary, timeout=150)
        self.assertLess((self.certificate / "Main.lean").stat().st_size, 180000)

    def test_partial_final_cuda_warp(self):
        source, reference, task = sources(7, 65, "cuda")
        case = self.root / "partial"
        write_case(case, source, reference, task)
        out = self.root / "partial-certificate"
        report = silu.verify(
            case / "kernel.cu",
            case / "reference.py",
            case / "task.json",
            out,
            lean=self.binary,
            timeout=150,
        )
        self.assertEqual(report["status"], "verified")
        self.assertEqual((report["block"], report["warp"]), (65, 32))
        check(out, lean=self.binary, timeout=150)

    def test_reference_precision_and_output_coverage_refusals(self):
        source, reference, task = sources(64, 4097)
        bad = [
            reference.replace("))).half()", ")))", 1),
            reference.replace(
                "return (activated.float() * (up + 0.0)).half()",
                "return (activated.float() * (up + 0.0)).half().select(0, 0)",
            ),
            reference.replace("reshape(64, 2, 4097)", "reshape(1, 2, 262208)"),
            reference.replace(
                "return (activated.float()", "return (activated.select(1, 0).float()"
            ),
        ]
        for candidate in bad:
            with self.subTest(candidate=candidate), self.assertRaises(Refusal):
                silu.prepare(source, candidate, json.dumps(task))

    def test_source_launch_and_bounds_refusals(self):
        source, reference, task = sources(64, 4097)
        for old, new in [
            ("idx + blockDim.x", "idx + 1"),
            ("idx + 4097]", "idx + 4096]"),
            ("idx < 4097", "idx < 4096"),
        ]:
            with self.subTest(mutation=old), self.assertRaises(Refusal):
                silu.prepare(source.replace(old, new), reference, json.dumps(task))
        candidates = []
        for path, value in [
            (("launch", "block"), 512),
            (("launch", "warp"), 32),
            (("launch", "grid"), True),
            (("fuel", 0), 1),
            (("buffers", 1, "dtype"), "float32"),
            (("buffers", 0, "shape", 0), True),
            (("buffers", 1, "shape", 1), 8193),
        ]:
            bad = json.loads(json.dumps(task))
            parent = bad
            for part in path[:-1]:
                parent = parent[part]
            parent[path[-1]] = value
            candidates.append(bad)
        for candidate in candidates:
            with self.subTest(task=candidate), self.assertRaises(Refusal):
                silu.prepare(source, reference, json.dumps(candidate))
        for rows, width in ((1, 4096), (1, 1073741825)):
            _, _, bad = sources(rows, width)
            with self.subTest(shape=(rows, width)), self.assertRaises(Refusal):
                silu.parse_task(json.dumps(bad))

    def test_direct_lean_rejects_removed_reference_rounding(self):
        source, reference, task = sources(64, 4097)
        task, tr, ref = silu.prepare(source, reference, json.dumps(task))

        def drop(n):
            if n.op == "un" and n.args[0] == "fromHalf":
                inner = n.args[1]
                if inner.op == "un" and inner.args[0] == "toHalf":
                    return inner.args[1]
            return Node(n.op, tuple(drop(a) if isinstance(a, Node) else a for a in n.args))

        bad = drop(ref)
        self.assertNotEqual(bad, ref)
        path = self.root / "direct-negative"
        path.mkdir()
        (path / "Main.lean").write_text(silu.render(task, tr, bad))
        accepted, log = run_lean(path, self.binary, 150)
        self.assertFalse(accepted)
        self.assertIn("error:", log)
        self.assertNotIn("Lean timed out", log)

    def test_rehashed_reference_tamper_fails_fixed_grammar(self):
        path = self.root / "rehashed"
        shutil.copytree(self.certificate, path)
        ref = path / "reference.py"
        original = ref.read_text()
        changed = original.replace("))).half()", ")))", 1)
        self.assertNotEqual(original, changed)
        ref.write_text(changed)
        report = json.loads((path / "report.json").read_text())
        report["files"]["reference.py"] = digest(ref.read_bytes())
        (path / "report.json").write_text(json.dumps(report))
        with self.assertRaises(Refusal) as raised:
            check(path, lean=self.binary, timeout=150)
        self.assertEqual(raised.exception.code, "silu-reference")

    def test_billion_cell_symbolic_contract_without_enumeration(self):
        source, reference, task = sources(1, 1073741823)
        case = self.root / "symbolic"
        write_case(case, source, reference, task)
        out = self.root / "symbolic-certificate"
        report = silu.verify(
            case / "kernel.cu",
            case / "reference.py",
            case / "task.json",
            out,
            lean=self.binary,
            timeout=150,
        )
        self.assertEqual(report["status"], "verified")
        self.assertEqual(report["input_elements"], 2147483646)
        self.assertLess((out / "Main.lean").stat().st_size, 180000)


if __name__ == "__main__":
    unittest.main()
