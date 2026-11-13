import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from reproduction.local_models import cuda_shape, full_shape


class CudaModelPreparationTests(unittest.TestCase):
    def test_existing_shapes_dtypes_and_fuels_are_preserved_across_backends(self):
        cases = cuda_shape.cuda_cases()
        self.assertEqual(len(cases), 17)
        self.assertEqual([c[:2] for c in cases], [c[:2] for c in full_shape.benchmark.CASES])
        for _, _, directory in cases:
            folder = cuda_shape.ROOT / "reproduction" / directory
            hip = Path(*("hip" if p == "cuda" else p for p in folder.parts))
            for path in folder.glob("*task.json"):
                with self.subTest(path=path):
                    task = json.loads(path.read_text())
                    counterpart = json.loads((hip / path.name).read_text())
                    self.assertEqual(task["language"], "cuda")
                    self.assertEqual(task["launch"]["warp"], 32)
                    self.assertEqual(task["buffers"], counterpart["buffers"])
                    self.assertEqual(task["fuel"], counterpart["fuel"])

    def test_model_main_exposes_four_holes_and_fixed_limits(self):
        block, owned = cuda_shape.sdk_case(cuda_shape.cuda_cases()[0])
        masked = {name: "by fail" for name in full_shape.SLOTS}
        main = full_shape.render(block, masked)
        spans = full_shape.proof_spans(main)
        self.assertEqual({n: s["sdk_positive_control"] for n, s in spans.items()}, masked)
        self.assertEqual(main.count("set_option maxRecDepth 10000"), 1)
        self.assertEqual(main.count("set_option maxHeartbeats 2000000"), 1)
        self.assertTrue(all("/cuda/" in name for name in owned))
        with self.assertRaisesRegex(ValueError, "CUDA case"):
            cuda_shape.sdk_case(full_shape.benchmark.CASES[0])

    def test_mixed_source_and_wrong_warp_tasks_are_refused_before_translation(self):
        case = cuda_shape.cuda_cases()[0]
        original = cuda_shape.ROOT / "reproduction" / case[2]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "reproduction" / case[2]
            shutil.copytree(original, target)
            with patch.object(cuda_shape, "ROOT", root):
                (target / "unexpected.hip").write_text("not a CUDA source")
                with self.assertRaisesRegex(ValueError, "Mixed"):
                    cuda_shape.sdk_case(case)
                (target / "unexpected.hip").unlink()
                path = target / "task.json"
                task = json.loads(path.read_text())
                task["launch"]["warp"] = 64
                path.write_text(json.dumps(task))
                with self.assertRaisesRegex(ValueError, "warp"):
                    cuda_shape.sdk_case(case)


if __name__ == "__main__":
    unittest.main()
