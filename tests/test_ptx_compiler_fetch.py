"""Compiler downloads stay hash-pinned data with closed archive paths."""

from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from reproduction.ptx import fetch_compiler as subject


class CompilerFetchTests(unittest.TestCase):
    def fetch_fixture(self, root, member, *, corrupt=False):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            archive.writestr(member, b"raise RuntimeError('wheel data must not execute')\n")
        content = buffer.getvalue()
        expected = hashlib.sha256(content).hexdigest()
        metadata = json.dumps({"urls": [{
            "filename": "fixture-manylinux_x86_64.whl",
            "digests": {"sha256": expected},
            "url": "https://files.pythonhosted.org/fixture.whl",
        }]}).encode()
        responses = [io.BytesIO(metadata), io.BytesIO(content + (b"changed" if corrupt else b""))]
        with patch.object(subject, "WHEELS", {"fixture": ("1", expected)}), \
                patch.object(subject.urllib.request, "urlopen", side_effect=responses) as network, \
                redirect_stdout(io.StringIO()):
            subject.fetch(root)
        self.assertEqual(network.call_count, 2)
        self.assertTrue(all(call.kwargs == {"timeout": 30} for call in network.call_args_list))

    def test_verified_wheel_is_extracted_as_data(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "compiler"
            self.fetch_fixture(root, "nvidia/fixture/code.py")
            self.assertIn("must not execute", (root / "packages/nvidia/fixture/code.py").read_text())
            report = json.loads((root / "downloads.json").read_text())
            self.assertEqual(report[0]["status"], "downloaded-and-hash-verified")
            self.assertIs(report[0]["tls_verification"], True)

    def test_changed_download_is_refused_before_extraction(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "compiler"
            with self.assertRaisesRegex(ValueError, "Downloaded compiler wheel differs"):
                self.fetch_fixture(root, "nvidia/fixture/code.py", corrupt=True)
            self.assertFalse((root / "packages").exists())
            self.assertEqual(json.loads((root / "downloads.json").read_text())[0]["status"], "failed")

    def test_traversal_is_refused_even_with_the_expected_fixture_digest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "compiler"
            with self.assertRaisesRegex(ValueError, "Unsafe wheel paths"):
                self.fetch_fixture(root, "../escaped.py")
            self.assertFalse((Path(temporary) / "escaped.py").exists())
            self.assertFalse((root / "packages").exists())


if __name__ == "__main__":
    unittest.main()
