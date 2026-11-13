"""Check the compiler-input boundary and keep reader acceptance separate from proof."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from reproduction.ptx import compile_full_shape as subject


class FullShapePtxCompileTests(unittest.TestCase):
    def test_translated_reader_result_does_not_claim_a_certificate(self):
        folder = subject.ROOT / "reproduction/ptx/cases/copy"
        task = json.loads((folder / "task.json").read_text())
        task["launch"]["warp"] = 32
        result = subject.reader_probe((folder / "kernel.ptx").read_text(), task)
        self.assertEqual(result["status"], "reader-translated-only")
        self.assertFalse(result["certificate_profile_validated"])
        self.assertFalse(result["formal_proof"])

    def test_reader_refusal_does_not_claim_a_false_kernel(self):
        folder = subject.ROOT / "reproduction/ptx/cases/relu"
        task = json.loads((folder / "task.json").read_text())
        task["launch"]["warp"] = 32
        for buffer in task["buffers"]:
            buffer["dtype"] = "float16"
        result = subject.reader_probe((folder / "kernel.ptx").read_text(), task)
        self.assertEqual((result["status"], result["code"]), ("reader-refused", "ptx-type"))
        self.assertFalse(result["formal_proof"])
        self.assertNotIn("counterexample", result)

    def test_changed_or_extra_extracted_headers_are_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            name = "nvidia/compiler/include/input.h"
            content = b"// closed compiler-input fixture\n"
            with zipfile.ZipFile(root / "fixture.whl", "w") as archive:
                archive.writestr(name, content)
            digest = hashlib.sha256((root / "fixture.whl").read_bytes()).hexdigest()
            (root / "downloads.json").write_text(json.dumps([{
                "package": "fixture", "version": "1", "sha256": digest,
                "status": "downloaded-and-hash-verified", "filename": "fixture.whl",
            }]))
            header = root / "packages" / name
            header.parent.mkdir(parents=True)
            header.write_bytes(content)
            with patch.dict(subject.WHEELS, {"fixture": ("1", digest)}, clear=True):
                _, bindings = subject.verify_toolchain(root)
                self.assertEqual(set(bindings), {name})
                extra = header.with_name("shadow.h")
                extra.write_text("// unexpected include\n")
                with self.assertRaisesRegex(ValueError, "Unexpected extracted"):
                    subject.verify_toolchain(root)
                extra.unlink()
                header.write_text("// changed header\n")
                with self.assertRaisesRegex(ValueError, "Changed extracted"):
                    subject.verify_toolchain(root)


if __name__ == "__main__":
    unittest.main()
