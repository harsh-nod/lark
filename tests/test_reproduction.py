import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from lark_kernels.frontend import translate
from lark_kernels.ir import Refusal, Task
from lark_kernels.machine import Machine, preflight
from lark_kernels.spec import read_spec
from lark_kernels.spec import Tensor
from lark_kernels.ir import literal
from reproduction.catalog import NAMES, SHAPES
from reproduction.run_cpu import FAMILIES, MUTATIONS
from lark_kernels.certificate import verify

ROOT = Path(__file__).resolve().parent.parent / "reproduction"
LEAN = os.environ.get("LARK_LEAN") or shutil.which("lean")


class ReproductionTests(unittest.TestCase):
    def test_multiaxis_broadcast_uses_trailing_dimensions(self):
        a = Tensor((2, 1, 3), tuple(literal(i) for i in range(6)))
        b = Tensor((1, 4, 1), tuple(literal(i * 10) for i in range(4)))
        result = a.binary("add", b)
        self.assertEqual(result.shape, (2, 4, 3))
        from tools.check_torch import evaluate

        self.assertEqual(
            [evaluate(x, {}) for x in result.values],
            [i * 3 + k + j * 10 for i in range(2) for j in range(4) for k in range(3)],
        )
        with self.assertRaises(Refusal):
            a.binary("add", Tensor((2, 2), tuple(literal(i) for i in range(4))))

    def test_bmm_rejects_rank_two_inputs(self):
        task = Task.read(ROOT / "cases/gemm/task.json")
        with self.assertRaisesRegex(Refusal, "rank-3"):
            read_spec("import torch\ndef reference(a,b):\n return torch.bmm(a,b)\n", task)

    def test_convolution_rejects_incompatible_groups(self):
        task = Task.read(ROOT / "cases/conv2d/task.json")
        with self.assertRaisesRegex(Refusal, "groups"):
            read_spec(
                "import torch\ndef reference(x,w):\n return torch.conv2d(x,w,groups=3)\n", task
            )

    def test_reduced_cases_match_independent_specs(self):
        for name in (*FAMILIES, "barrier_sum", "llmc_fixed"):
            p = ROOT / "cases" / name
            t = Task.read(p / "task.json")
            with self.subTest(task=name):
                tr = translate((p / "kernel.hip").read_text(), t)
                preflight(t, tr, read_spec((p / "reference.py").read_text(), t))

    def test_mutants_are_nontrivial_and_preflight_rejects_each(self):
        for name, rules in MUTATIONS.items():
            p = ROOT / "cases" / name
            t = Task.read(p / "task.json")
            source = (p / "kernel.hip").read_text()
            spec = read_spec((p / "reference.py").read_text(), t)
            for rule, a, b in rules:
                with self.subTest(task=name, rule=rule), self.assertRaises(Refusal):
                    self.assertIn(a, source)
                    preflight(t, translate(source.replace(a, b, 1), t), spec)

    def test_benign_race_survives_symbolic_numerical_equivalence(self):
        p = ROOT / "cases/llmc_race"
        t = Task.read(p / "task.json")
        m = Machine(t, translate((p / "kernel.hip").read_text(), t)).run()
        self.assertEqual(m.outputs(), read_spec((p / "reference.py").read_text(), t))
        a, b = m.race()
        self.assertEqual({a.thread, b.thread}, {2, 3})
        self.assertEqual(a.location, ("global", 0, 1, 2))

    def test_pinned_upstream_matches_recorded_hash(self):
        import hashlib

        source = ROOT / "upstream/llmc_softmax_kernel7.cu"
        metadata = json.loads((ROOT / "upstream/llmc-provenance.json").read_text())
        self.assertEqual(
            hashlib.sha256(source.read_bytes()).hexdigest(), metadata["excerpt_sha256"]
        )

    def test_paper_shape_catalog_covers_seventeen_distinct_tasks(self):
        self.assertEqual(len(set(NAMES)), 17)
        self.assertEqual(set(NAMES), set(SHAPES))
        self.assertEqual(SHAPES["batchmatmul"][0][0], (32, 64, 256))


@unittest.skipUnless(LEAN, "Lean 4.19.0 is required")
class ReproductionLeanTests(unittest.TestCase):
    def test_new_reference_families_certify(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in ("batchmatmul", "conv2d", "depthwise_conv"):
                case = ROOT / "cases" / name
                with self.subTest(task=name):
                    result = verify(
                        case / "kernel.hip",
                        case / "reference.py",
                        case / "task.json",
                        Path(tmp) / name,
                        lean=LEAN,
                    )
                    self.assertEqual(result["status"], "verified")


if __name__ == "__main__":
    unittest.main()
