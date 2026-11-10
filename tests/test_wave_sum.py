import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels import collective, wave_sum
from lark_kernels.certificate import check, lean_binary
from lark_kernels.ir import Refusal, node

ROOT = Path(__file__).resolve().parents[1]
CASE = ROOT / "reproduction/wave_reduction/cases/sum64"
ENABLED = os.environ.get("LARK_TEST_REAL") == "1"


def sources():
    return [(CASE / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")]


class WaveSumReaderTests(unittest.TestCase):
    def test_full_program_and_all_reference_cells(self):
        task, tr, refs = wave_sum.prepare(*sources())
        self.assertEqual(tr.program, wave_sum.expected_program())
        self.assertEqual(len(refs), 64)
        self.assertEqual(len(collective.Machine(task, tr).run().trace), 128)
        self.assertEqual(task.fuel, (4, 7, 1, 1))

    def test_changed_reference_source_geometry_and_precision_refused(self):
        source, reference, task = sources()
        for changed in (
            reference.replace("sum(dim=0", "sum(dim=1"),
            reference.replace("return input.sum", "return 1 + input.sum"),
            reference.replace("repeat_interleave(64", "repeat_interleave(63"),
            reference.replace("import torch", "import os\nimport torch"),
        ):
            with self.subTest(reference=changed), self.assertRaises(Refusal):
                wave_sum.prepare(source, changed, task)
        with self.assertRaises(Refusal):
            wave_sum.prepare(
                source.replace("__shfl_xor(x, 1, 64)", "__shfl_xor(x, 2, 64)"), reference, task
            )
        for change in ("cuda", "half", "block", "boolean", "fuel"):
            data = json.loads(task)
            if change == "cuda":
                data["language"] = "cuda"
            elif change == "half":
                data["buffers"][0]["dtype"] = "float16"
            elif change == "block":
                data["launch"]["block"] = 128
            elif change == "boolean":
                data["launch"]["grid"] = True
            else:
                data["fuel"][1] = 8
            with self.subTest(change=change), self.assertRaises(Refusal):
                wave_sum.prepare(source, reference, json.dumps(data))


@unittest.skipUnless(ENABLED, "optional Mathlib checks run with LARK_TEST_REAL=1")
class WaveSumProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="lark-wave-sum-test-")
        cls.root = Path(cls.temporary.name)
        cls.lean = lean_binary()
        cls.cert = cls.root / "certificate"
        # Keep CRLF bytes and comments distinct from the lowering/proof content.
        kernel = cls.root / "kernel.hip"
        kernel.write_bytes(
            ("// source byte preservation\n" + sources()[0]).replace("\n", "\r\n").encode()
        )
        cls.report = wave_sum.verify(
            kernel,
            CASE / "reference.py",
            CASE / "task.json",
            cls.cert,
            lean=cls.lean,
            timeout=300,
        )
        if cls.report["status"] != "verified":
            raise AssertionError((cls.cert / "lean-1.log").read_text())

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_export_and_fresh_global_check(self):
        self.assertIn(b"\r\n", (self.cert / "kernel.hip").read_bytes())
        log = check(self.cert, lean=self.lean, timeout=300)
        self.assertIn("'LarkCertificate.kernel_eq_spec'", log)
        self.assertNotIn("sorryAx", log)
        self.assertEqual(self.report["model_calls"], 0)

    def test_last_reference_cell_change_is_rejected_by_lean(self):
        task, tr, refs = wave_sum.prepare(*sources())
        refs[63] = node("input", 0, 0)
        accepted, log = wave_sum.validate_main(
            wave_sum.render(task, tr, refs).encode(), self.lean, 300
        )
        self.assertFalse(accepted)
        self.assertIn("reference_63", log)
        self.assertIn("error:", log)
        self.assertNotIn("Lean timed out", log)

    def test_wrong_shuffle_is_rejected_by_lean(self):
        source, reference, task_source = sources()
        task, _, refs = wave_sum.prepare(source, reference, task_source)
        changed = source.replace("__shfl_xor(x, 1, 64)", "__shfl_xor(x, 2, 64)")
        tr = collective.translate(changed, task)
        accepted, log = wave_sum.validate_main(
            wave_sum.render(task, tr, refs).encode(), self.lean, 300
        )
        self.assertFalse(accepted)
        self.assertIn("program", log)
        self.assertIn("error:", log)
        self.assertNotIn("Lean timed out", log)

    def test_fully_rehashed_reference_change_fails_global_check(self):
        changed = self.root / "changed-reference"
        shutil.copytree(self.cert, changed)
        p = changed / "reference.py"
        p.write_text(p.read_text().replace("return input.sum", "return 1 + input.sum"))
        report = json.loads((changed / "report.json").read_text())
        report["files"]["reference.py"] = hashlib.sha256(p.read_bytes()).hexdigest()
        (changed / "report.json").write_text(json.dumps(report))
        with self.assertRaises(Refusal):
            check(changed, lean=self.lean, timeout=300)

    def test_certificate_build_files_and_cached_objects_are_ignored(self):
        changed = self.root / "extra-build-files"
        shutil.copytree(self.cert, changed)
        marker = self.root / "untrusted-config-executed"
        (changed / "lakefile.lean").write_text(
            "import Lake\n#eval IO.FS.writeFile " + json.dumps(str(marker)) + ' "unexpected"\n'
        )
        fake = changed / ".lake/build/lib/lean/LarkReal/WaveSum.olean"
        fake.parent.mkdir(parents=True)
        fake.write_bytes(b"not an imported proof object")
        log = check(changed, lean=self.lean, timeout=300)
        self.assertNotIn("sorryAx", log)
        self.assertFalse(marker.exists())


if __name__ == "__main__":
    unittest.main()
