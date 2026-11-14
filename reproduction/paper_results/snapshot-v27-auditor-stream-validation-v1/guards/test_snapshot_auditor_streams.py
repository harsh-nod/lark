"""Same frozen auditor, complete tar payloads and independent refusal checks."""

import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest

from reproduction.paper_results import replay_snapshot as replay


class AuditorStreamTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lark-auditor-streams-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def raw_tar(self):
        output = io.BytesIO()
        expected = {"empty": b"", "source.py": b"raise RuntimeError('data must remain data')\n",
                    "retained/history.bin": bytes(range(256)) * 8192}
        with tarfile.open(fileobj=output, mode="w") as archive:
            for name, value in expected.items():
                info = tarfile.TarInfo(name)
                info.size = len(value)
                archive.addfile(info, io.BytesIO(value))
        return output.getvalue(), expected

    def decoded_entries(self, encoded, opener, **kwargs):
        with gzip.GzipFile(fileobj=io.BytesIO(encoded)) as decoded, \
                opener(fileobj=decoded, mode="r|", **kwargs) as archive:
            output = {}
            for member in archive:
                replay.safe_path(member.name)
                if not member.isfile() or member.size > 10_000_000:
                    raise ValueError("Unsafe bounded archive member")
                value = archive.extractfile(member).read()
                self.assertEqual(len(value), member.size)
                output[member.name] = value
        return output

    def test_all_streamed_bytes_and_headers_match_the_original_parser(self):
        raw, expected = self.raw_tar()
        encoded = gzip.compress(raw, mtime=0)
        self.assertEqual(self.decoded_entries(encoded, replay.auditor_tar_open), expected)
        self.assertEqual(self.decoded_entries(encoded, tarfile.open), expected)

    def test_concatenated_gzip_stream_keeps_every_member_and_empty_payload(self):
        raw, expected = self.raw_tar()
        encoded = b"".join(gzip.compress(raw[i:i+65536], mtime=0)
                           for i in range(0, len(raw), 65536))
        self.assertEqual(self.decoded_entries(encoded, replay.auditor_tar_open), expected)

    def test_explicit_small_buffer_and_seekable_mode_keep_their_existing_behavior(self):
        raw, expected = self.raw_tar()
        encoded = gzip.compress(raw, mtime=0)
        with gzip.GzipFile(fileobj=io.BytesIO(encoded)) as decoded, \
                replay.auditor_tar_open(fileobj=decoded, mode="r|", bufsize=2048) as archive:
            self.assertEqual(archive.fileobj.bufsize, 2048)
            self.assertEqual({m.name: archive.extractfile(m).read() for m in archive}, expected)
        with replay.auditor_tar_open(fileobj=io.BytesIO(encoded), mode="r:gz") as archive:
            self.assertEqual({m.name: archive.extractfile(m).read() for m in archive}, expected)

    def test_traversal_links_and_oversized_headers_still_reach_the_refusal_checks(self):
        for name, kind, size in [("../escape", tarfile.REGTYPE, 1),
                                 ("link", tarfile.SYMTYPE, 0),
                                 ("oversized", tarfile.REGTYPE, 10_000_001)]:
            info = tarfile.TarInfo(name)
            info.type, info.size = kind, size
            info.linkname = "../escape" if kind == tarfile.SYMTYPE else ""
            raw = info.tobuf() + b"x" + b"\0" * 2048
            for opener in (tarfile.open, replay.auditor_tar_open):
                with self.subTest(name=name, opener=opener), self.assertRaises(ValueError):
                    self.decoded_entries(gzip.compress(raw, mtime=0), opener)

    def auditor_fixture(self):
        script = self.root / "reproduction/paper_results/audit.py"
        script.parent.mkdir(parents=True)
        script.write_text("""import gzip, io, json, sys, tarfile
from pathlib import Path
with gzip.GzipFile(fileobj=io.BytesIO(gzip.compress(b'\\0' * 10240))) as decoded:
    with tarfile.open(fileobj=decoded, mode='r|') as archive:
        buffer = archive.fileobj.bufsize
print(json.dumps({'argv':sys.argv, 'root':str(Path(__file__).resolve().parents[2]),
                  'buffer':buffer, 'auditor_import_path':sys.path[0]}))
""")
        return script

    def launch(self, script, sha):
        env = {k: v for k, v in os.environ.items() if k not in ("PYTHONPATH", "LEAN_PATH")}
        env["PATH"] = "/nonexistent"
        return subprocess.run([sys.executable, "-I", str(Path(replay.__file__).resolve()),
                               "--_frozen-auditor", str(script), sha,
                               "--source-archive", "manuscript-as-data.tar", "--check"],
                              cwd=self.root, env=env, capture_output=True, text=True, timeout=30)

    def test_child_retains_source_argv_and_root_without_importing_captured_cwd_modules(self):
        script = self.auditor_fixture()
        (self.root / "tarfile.py").write_text("raise RuntimeError('captured cwd module executed')\n")
        result = self.launch(script, hashlib.sha256(script.read_bytes()).hexdigest())
        self.assertEqual(result.returncode, 0, result.stderr)
        row = json.loads(result.stdout)
        self.assertEqual(row["argv"], [str(script), "--source-archive", "manuscript-as-data.tar", "--check"])
        self.assertEqual(row["root"], str(self.root))
        self.assertEqual(row["auditor_import_path"], str(script.parent))
        self.assertEqual(row["buffer"], 1024 * 1024)

    def test_child_refuses_changed_auditor_before_execution(self):
        script = self.auditor_fixture()
        result = self.launch(script, "0" * 64)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("Frozen auditor bytes differ", result.stderr)


if __name__ == "__main__":
    unittest.main()
