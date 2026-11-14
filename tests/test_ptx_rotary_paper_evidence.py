"""Recorded RoPE evidence, coherent forgeries and inert captured source."""

import copy
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from reproduction.paper_results.ptx_rotary_evidence import (
    ROOT, Recording, check_recording_packet,
)


PACKET = ROOT / "reproduction/ptx/results/full-size-rotary-proof-v1"


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def sha(value):
    return hashlib.sha256(value).hexdigest()


class RotaryEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reader = Recording(PACKET, "rotary")
        with tarfile.open(PACKET / "export.tar.gz", mode="r|gz") as archive:
            cls.export = {member.name: archive.extractfile(member).read() for member in archive}

    def changed(self, mutation):
        entries = dict(self.export)
        result = json.loads(entries["results.json"])
        mutation(result, entries)
        entries["results.json"] = encoded(result)
        entries["manifest.json"] = encoded({n: sha(v) for n, v in entries.items() if n != "manifest.json"})
        return entries

    def test_complete_packet_all_positives_controls_and_failed_history(self):
        report = check_recording_packet(PACKET)
        self.assertEqual(report["independent_source_bound_development_proofs"], 1)
        self.assertEqual(report["retained_positive_Main_checks"], 4)
        self.assertEqual(report["fresh_owned_module_builds"], 32)
        self.assertEqual(report["direct_Lean_negative_controls"], 4)
        self.assertEqual(report["coherently_rehashed_negative_controls"], 17)
        self.assertEqual(report["failed_development_checks"], 11)
        self.assertFalse(report["captured_code_executed"])
        self.assertFalse(report["original_paper_fully_reproduced"])

    def test_coherent_boolean_scope_limit_and_execution_forgeries_are_refused(self):
        changes = [
            {"source_bound_development_proofs": True},
            {"owned_Lean_modules_freshly_compiled": 8.0},
            {"launch": {"grid": 32768, "block": True, "warp": 32}},
            {"unchanged_CUDA_contract_fuel": [8, True, 1, 1]},
            {"nvidia_execution": True},
            {"original_paper_fully_reproduced": True},
            {"old_owned_olean_cache_used": True},
            {"limits": {**self.reader.protocol["contract"]["limits"], "maxHeartbeats": 4000000}},
        ]
        for change in changes:
            with self.subTest(change=change):
                entries = self.changed(lambda result, _: result.update(copy.deepcopy(change)))
                with self.assertRaisesRegex(ValueError, "positive.*(scope|counters|binding) differ"):
                    self.reader.positive(entries)

    def test_missing_independent_tensor_denotation_audit_is_refused(self):
        def mutation(result, _):
            del result["axiom_audits"]["LarkPtxRotaryCertificate.reference_denotation"]

        with self.assertRaisesRegex(ValueError, "positive axiom audit differs"):
            self.reader.positive(self.changed(mutation))

    def test_coherently_rehashed_forbidden_axiom_is_refused(self):
        def mutation(result, entries):
            entries["Main.log"] = entries["Main.log"].replace(b"Quot.sound", b"sorryAx", 1)
            result["main_check"]["log_sha256"] = sha(entries["Main.log"])

        with self.assertRaisesRegex(ValueError, "positive Lean log contains an error or unproved axiom"):
            self.reader.positive(self.changed(mutation))

    def test_captured_python_is_inert_and_cannot_replace_the_trusted_sdk(self):
        with tempfile.TemporaryDirectory(prefix="lark-rotary-inert-source-") as temporary:
            marker = Path(temporary) / "captured-code-executed"

            def mutation(result, entries):
                name = "python/ptx_rotary_certificate.py"
                path = "owned-sources/" + name
                entries[path] += ("\nfrom pathlib import Path\nPath(" + repr(str(marker)) + ").touch()\n").encode()
                bindings = json.loads(entries["source-bindings.json"])
                bindings[name] = sha(entries[path])
                entries["source-bindings.json"] = encoded(bindings)
                result["source_bindings_sha256"] = sha(entries["source-bindings.json"])

            with self.assertRaisesRegex(ValueError, "positive source/contract/proof binding differs"):
                self.reader.positive(self.changed(mutation))
            self.assertFalse(marker.exists())

    def test_tar_symlinks_and_traversal_are_refused_without_extraction(self):
        for hostile in ("symlink", "traversal"):
            with self.subTest(hostile=hostile):
                data = io.BytesIO()
                entries = dict(self.export)
                name = next(iter(entries))
                if hostile == "traversal":
                    entries["../outside"] = entries.pop(name)
                inventory = encoded({n: sha(v) for n, v in entries.items()})
                with tarfile.open(fileobj=data, mode="w:gz") as archive:
                    for i, (path, value) in enumerate(entries.items()):
                        member = tarfile.TarInfo(path)
                        member.size = len(value)
                        if hostile == "symlink" and i == 0:
                            member.type, member.linkname, member.size = tarfile.SYMTYPE, "/tmp/outside", 0
                            archive.addfile(member)
                        else:
                            archive.addfile(member, io.BytesIO(value))
                raw = data.getvalue()
                reader = Recording(PACKET, "rotary")
                reader.content = {"export.tar.gz": raw, "export-files.json": inventory}.__getitem__
                binding = {"files": len(entries), "archive_bytes": len(raw),
                           "uncompressed_bytes": sum(map(len, entries.values())),
                           "archive_sha256": sha(raw), "inventory_sha256": sha(inventory)}
                with self.assertRaisesRegex(ValueError, "unsafe (archive member|recording path)"):
                    reader.archive("export", binding)


if __name__ == "__main__":
    unittest.main()
