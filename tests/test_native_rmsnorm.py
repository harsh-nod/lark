import json
import os
from pathlib import Path
import re
import shutil
import tempfile
import unittest

from lark_kernels import native_rmsnorm, native_rmsnorm_certificate as native
from lark_kernels.certificate import check, digest
from lark_kernels.ir import Refusal, Task

CASE = Path(__file__).resolve().parents[1] / "reproduction/production_rmsnorm/cases/weighted_16384"


def task_for_rows(rows):
    data = json.loads((CASE / "task.json").read_text())
    data["buffers"][0]["shape"][0] = rows
    data["buffers"][1]["shape"][0] = rows
    data["launch"]["grid"] = rows
    return data


class NativeContractTests(unittest.TestCase):
    def test_large_profile_is_explicit_and_bounded(self):
        source = json.dumps(task_for_rows(255))
        task = native_rmsnorm.parse_task(source)
        self.assertEqual((task.grid, task.block, task.buffers[0].size), (255, 1024, 4177920))
        with self.assertRaises(Refusal):
            Task.parse(source)
        for rows in (0, 256, True):
            with self.subTest(rows=rows), self.assertRaises(Refusal):
                native_rmsnorm.parse_task(json.dumps(task_for_rows(rows)))

    def test_wrong_launch_dtype_and_weight_contracts(self):
        mutations = []
        for field, value in (("block", 256), ("warp", 32), ("grid", True)):
            data = task_for_rows(1)
            data["launch"][field] = value
            mutations.append(data)
        data = task_for_rows(1)
        data["buffers"][2]["shape"] = [1]
        mutations.append(data)
        data = task_for_rows(1)
        data["buffers"][0]["dtype"] = "float32"
        mutations.append(data)
        for data in mutations:
            with self.subTest(data=data), self.assertRaises(Refusal):
                native_rmsnorm.parse_task(json.dumps(data))

    def test_closed_reference_denies_changed_math(self):
        source = (CASE / "kernel.hip").read_text()
        reference = (CASE / "reference.py").read_text()
        task = (CASE / "task.json").read_text()
        native.prepare(source, reference, task)
        for changed in (
            reference.replace("dim=1", "dim=0"),
            reference.replace("1e-5", "1e-4"),
            reference.replace("weight.float()", "weight.float() * 2"),
        ):
            with self.subTest(reference=changed), self.assertRaises(Refusal):
                native.prepare(source, changed, task)
        for input_name, weight_name in (("torch", "weight"), ("input", "x"), ("torch", "x"), ("torch_", "torch")):
            with self.subTest(input_name=input_name, weight_name=weight_name):
                data = task_for_rows(1)
                data["buffers"][1]["name"] = input_name
                data["buffers"][2]["name"] = weight_name
                renamed = re.sub(r"\b(input|weight)\b", lambda m: {"input": input_name, "weight": weight_name}[m[0]], source)
                safe = native_rmsnorm.canonical_reference(input_name, weight_name)
                native.prepare(renamed, safe, json.dumps(data))
                unsafe = re.sub(r"\b(input|weight)\b", lambda m: {"input": input_name, "weight": weight_name}[m[0]], reference)
                with self.assertRaises(Refusal):
                    native.prepare(renamed, unsafe, json.dumps(data))


@unittest.skipUnless(os.environ.get("LARK_TEST_REAL") == "1", "requires pinned optional Mathlib dependencies/cache")
class NativeProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="lark-native-rmsnorm-tests-")
        cls.root = Path(cls.temporary.name)
        cls.baseline = cls.root / "baseline"
        report = native.verify(CASE / "kernel.hip", CASE / "reference.py", CASE / "task.json", cls.baseline, timeout=600)
        if report["status"] != "verified":
            raise AssertionError(report["axiom_audit"])

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_certificate_and_recheck_at_all_validation_row_counts(self):
        for rows in (1, 3, 64, 255):
            with self.subTest(rows=rows):
                if rows == 1:
                    output = self.baseline
                else:
                    task = self.root / f"rows-{rows}.json"
                    task.write_text(json.dumps(task_for_rows(rows)))
                    output = self.root / f"rows-{rows}"
                    report = native.verify(CASE / "kernel.hip", CASE / "reference.py", task, output, timeout=600)
                    self.assertEqual(report["status"], "verified", report["axiom_audit"])
                log = check(output, timeout=600)
                self.assertIn("LarkCertificate.kernel_eq_spec", log)
                self.assertNotIn("sorryAx", log)
                self.assertEqual(json.loads((output / "report.json").read_text())["output_elements"], rows * 16384)
        task = task_for_rows(1)
        task["buffers"][2]["name"] = "x"
        task_path = self.root / "named-weight.json"
        task_path.write_text(json.dumps(task))
        kernel = self.root / "named-weight.hip"
        kernel.write_text(re.sub(r"\bweight\b", "x", (CASE / "kernel.hip").read_text()))
        reference = self.root / "named-weight.py"
        reference.write_text(native_rmsnorm.canonical_reference("input", "x"))
        output = self.root / "named-weight"
        report = native.verify(kernel, reference, task_path, output, timeout=600)
        self.assertEqual(report["status"], "verified", report["axiom_audit"])
        self.assertIn("kernel_eq_spec", check(output, timeout=600))

    def test_modified_source_programs_are_rejected_directly_by_lean(self):
        source = (CASE / "kernel.hip").read_text()
        changes = {
            "shuffle": source.replace("__shfl_down(variance, 8, 16)", "__shfl_down(variance, 4, 16)"),
            "barrier": source.replace("  __syncthreads();", "", 1),
            "weight": source.replace("weight[outVector * 8 + outComponent]", "weight[0]"),
            "partial": source.replace("if (lane == 0) { partials[warp] = variance; }", "partials[warp] = variance;"),
        }
        for name, changed in changes.items():
            with self.subTest(control=name):
                kernel = self.root / f"{name}.hip"
                kernel.write_text(changed)
                report = native.verify(kernel, CASE / "reference.py", CASE / "task.json", self.root / f"control-{name}", timeout=600)
                self.assertEqual(report["status"], "unproved")
                self.assertIs(report["whole_launch_proved"], False)
                self.assertIn("program_data", report["axiom_audit"])
                self.assertIn("decide", report["axiom_audit"])
                self.assertNotIn("maximum", report["axiom_audit"])
                self.assertNotIn("Stack overflow", report["axiom_audit"])

    def test_rehashed_source_theorem_model_and_scope_tampering(self):
        mutations = {
            "theorem": ("Main.lean", lambda s: s.replace("Real.sqrt", "Real.exp")),
            "model": ("Lark/NativeRmsNormCorrect.lean", lambda s: s.replace("theorem correct", "theorem changed")),
            "reference": ("reference.py", lambda s: s.replace("dim=1", "dim=0")),
        }
        for name, (relative, mutation) in mutations.items():
            with self.subTest(control=name):
                output = self.root / f"tamper-{name}"
                shutil.copytree(self.baseline, output)
                path = output / relative
                path.write_text(mutation(path.read_text()))
                report = json.loads((output / "report.json").read_text())
                report["files"][relative] = digest(path.read_bytes())
                if relative in report["model_hashes"]:
                    report["model_hashes"][relative] = report["files"][relative]
                (output / "report.json").write_text(json.dumps(report))
                with self.assertRaises(Refusal):
                    check(output, timeout=600)
        for field, value in (("original_paper_fully_reproduced", True), ("scope", "all paper results"), ("output_elements", True)):
            with self.subTest(field=field):
                output = self.root / f"tamper-report-{field}"
                shutil.copytree(self.baseline, output)
                report = json.loads((output / "report.json").read_text())
                report[field] = value
                (output / "report.json").write_text(json.dumps(report))
                with self.assertRaises(Refusal):
                    check(output, timeout=600)

    def test_rehashed_task_cannot_rebind_the_proved_shape(self):
        output = self.root / "tamper-task"
        shutil.copytree(self.baseline, output)
        (output / "task.json").write_text(json.dumps(task_for_rows(3)))
        report = json.loads((output / "report.json").read_text())
        report["files"]["task.json"] = digest((output / "task.json").read_bytes())
        (output / "report.json").write_text(json.dumps(report))
        with self.assertRaises(Refusal):
            check(output, timeout=600)


if __name__ == "__main__":
    unittest.main()
