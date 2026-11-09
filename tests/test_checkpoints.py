import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from reproduction.local_models import checkpoint


class CheckpointTests(unittest.TestCase):
    def run_validation(self, root, corrupt=None):
        weights, config = b"recorded-weight-fixture", b'{"model_type":"fixture"}'
        (root / "weights.safetensors").write_bytes(
            weights if corrupt != "weights" else b"X" + weights[1:]
        )
        (root / "config.json").write_bytes(config if corrupt != "config" else b"X" + config[1:])
        info = SimpleNamespace(
            sha=checkpoint.MODELS["zai-org/GLM-5.3-Flash"],
            gated=False,
            siblings=[
                SimpleNamespace(
                    rfilename="weights.safetensors",
                    size=len(weights),
                    lfs=SimpleNamespace(sha256=hashlib.sha256(weights).hexdigest()),
                ),
                SimpleNamespace(
                    rfilename="config.json",
                    size=len(config),
                    lfs=None,
                    blob_id=hashlib.sha1(
                        b"blob " + str(len(config)).encode() + b"\0" + config
                    ).hexdigest(),
                ),
            ],
        )

        def snapshot(*args, **kwargs):
            self.assertTrue(kwargs["local_files_only"])
            return str(root)

        hub = SimpleNamespace(
            HfApi=lambda: SimpleNamespace(model_info=lambda *a, **k: info),
            snapshot_download=snapshot,
        )
        output = root / "checked.json"
        argv = ["checkpoint.py", "--cache", str(root), "--output", str(output), "--local-only"]
        with (
            patch.dict(sys.modules, {"huggingface_hub": hub}),
            patch.object(sys, "argv", argv),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            checkpoint.main()
        return json.loads(output.read_text())

    def test_weights_and_supporting_git_blobs_are_checked_offline(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = self.run_validation(Path(tmp))
            self.assertEqual(result["status"], "verified-download")
            self.assertEqual(len(result["weights"]), 1)
            self.assertEqual(len(result["supporting_files"]), 1)
            self.assertEqual(result["model_calls"], 0)

    def test_corrupted_weight_or_configuration_never_finishes_validation(self):
        for corrupt in ("weights", "config"):
            with self.subTest(corrupt=corrupt), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                with self.assertRaises(RuntimeError):
                    self.run_validation(root, corrupt)
                self.assertEqual(
                    json.loads((root / "checked.json").read_text())["status"], "checking"
                )


if __name__ == "__main__":
    unittest.main()
