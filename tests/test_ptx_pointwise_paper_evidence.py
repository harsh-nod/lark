"""Semantic scope controls against the actual recorded finite PTX proof packet."""

import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest

from reproduction.paper_results.ptx_pointwise_evidence import (
    CI, PREFIX, PUBLICATION, check_ptx_pointwise_evidence, check_recording_packet,
)


ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(data):
    return hashlib.sha256(data).hexdigest()


class PtxPointwisePaperEvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="lark-ptx-ledger-controls-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.packet = self.root / PREFIX
        shutil.copytree(ROOT / PREFIX, self.packet)
        shutil.copytree(ROOT / PUBLICATION, self.root / PUBLICATION)

    def rehash(self):
        write(self.packet / "manifest.json", {
            p.name: sha(p.read_bytes()) for p in sorted(self.packet.iterdir())
            if p.is_file() and p.name != "manifest.json"})

    def report(self, mutate):
        path = self.packet / "results.json"
        report = read(path)
        mutate(report)
        write(path, report)
        self.rehash()

    def archive(self, label, mutate, copied_summary=None):
        """Rehash archive members, all inner manifests, inventory and packet."""
        path = self.packet / (label + ".tar.gz")
        with tarfile.open(path) as archive:
            entries = {m.name: archive.extractfile(m).read() for m in archive.getmembers()}
        mutate(entries)
        manifests = [n for n in entries if n == "manifest.json" or n.endswith("/manifest.json")]
        for name in sorted(manifests, key=lambda n: n.count("/"), reverse=True):
            prefix = name[:-len("manifest.json")]
            values = {n[len(prefix):]: sha(data) for n, data in sorted(entries.items())
                      if n.startswith(prefix) and n != name}
            entries[name] = (json.dumps(values, indent=2) + "\n").encode()
        with path.open("wb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0, compresslevel=1) as zipped:
                with tarfile.open(fileobj=zipped, mode="w") as archive:
                    for name, data in sorted(entries.items()):
                        member = tarfile.TarInfo(name)
                        member.size = len(data)
                        archive.addfile(member, io.BytesIO(data))
        inventory = self.packet / (label + "-files.json")
        write(inventory, {n: sha(data) for n, data in sorted(entries.items())})
        if copied_summary:
            (self.packet / copied_summary).write_bytes(entries["results.json"])
        self.report(lambda report: report["archives"][label].update(
            files=len(entries), uncompressed_bytes=sum(map(len, entries.values())),
            archive_sha256=sha(path.read_bytes()), inventory_sha256=sha(inventory.read_bytes())))

    def refused(self, message):
        with self.assertRaisesRegex(ValueError, message):
            check_recording_packet(self.packet)

    def test_actual_packet_one_kernel_four_checks_and_no_experiments(self):
        report = check_recording_packet(self.packet)
        self.assertEqual(report["independent_source_bound_development_proofs"], 1)
        self.assertEqual(report["retained_positive_Main_checks"], 4)
        self.assertEqual(report["positive_rechecks"], 3)
        self.assertEqual(report["direct_Lean_negative_controls"], 4)
        self.assertIs(report["fresh_experiments_by_ledger"], False)
        self.assertIs(report["original_paper_fully_reproduced"], False)
        self.assertFalse((self.root / ".git").exists())

    def test_three_rechecks_cannot_be_counted_as_four_kernels(self):
        self.report(lambda report: report.update(independent_source_bound_development_proofs=4))
        self.refused("kernel/recheck/execution counters differ")

    def test_boolean_cannot_replace_one_kernel(self):
        self.report(lambda report: report.update(independent_source_bound_development_proofs=True))
        self.refused("kernel/recheck/execution counters differ")

    def test_original_result_and_nvidia_overclaims(self):
        for field in ("original_paper_fully_reproduced", "nvidia_execution"):
            original = (self.packet / "results.json").read_bytes()
            self.report(lambda report: report.update({field: True}))
            self.refused("proof contract/original scope differs")
            (self.packet / "results.json").write_bytes(original)
            self.rehash()

    def test_raised_proof_budget(self):
        self.report(lambda report: report["limits"].update(maxHeartbeats=4000000))
        self.refused("proof contract/original scope differs")

    def test_erased_trusted_correspondence(self):
        self.report(lambda report: report.update(scope="Complete IEEE/NVIDIA proof"))
        self.refused("proof contract/original scope differs")

    def test_relabelled_reference_or_weakened_shape(self):
        self.report(lambda report: report.update(elements=16))
        self.refused("kernel/recheck/execution counters differ")

    def test_nested_positive_cannot_claim_old_import_cache(self):
        def mutate(entries):
            proof = json.loads(entries["results.json"])
            proof["old_owned_olean_cache_used"] = True
            entries["results.json"] = (json.dumps(proof, indent=2) + "\n").encode()
        self.archive("replay", mutate)
        self.refused("positive source/contract/proof binding differs")

    def test_positive_custom_axiom_even_with_matching_edited_log(self):
        def mutate(entries):
            proof = json.loads(entries["results.json"])
            proof["axiom_audits"]["LarkPtxCertificate.kernel_eq_spec"].append("custom_axiom")
            log = entries["Main.log"].decode().replace(
                "'LarkPtxCertificate.kernel_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]",
                "'LarkPtxCertificate.kernel_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound, custom_axiom]")
            entries["Main.log"] = log.encode()
            proof["main_check"]["log_sha256"] = sha(entries["Main.log"])
            entries["results.json"] = (json.dumps(proof, indent=2) + "\n").encode()
        self.archive("export", mutate)
        self.refused("positive axiom audit differs")

    def test_preflight_refusal_cannot_replace_direct_lean_control(self):
        def mutate(entries):
            report = json.loads(entries["results.json"])
            report["negative_controls"][0]["reader_accepted"] = False
            entries["results.json"] = (json.dumps(report, indent=2) + "\n").encode()
        self.archive("controls", mutate, "controls-results.json")
        self.refused("direct Lean binding-control scope differs")

    def test_installed_wheel_cannot_import_checkout(self):
        def mutate(entries):
            report = json.loads(entries["results.json"])
            report["checkout_imported"] = True
            entries["results.json"] = (json.dumps(report, indent=2) + "\n").encode()
        self.archive("installed-wheel", mutate, "installed-wheel-results.json")
        self.refused("installed-wheel replay differs")

    def test_missing_actual_ci_cannot_satisfy_final_ledger(self):
        declared = [str(p.relative_to(self.root)) for p in self.root.rglob("*") if p.is_file()]
        config = {"evidence_groups": {"ptx_pointwise_proof": declared},
                  "ptx_pointwise_proof": {"prefix": PREFIX, "publication_prefix": PUBLICATION, "ci_prefix": CI}}
        with self.assertRaisesRegex(ValueError, "auxiliary evidence path differs"):
            check_ptx_pointwise_evidence(config, self.root)


if __name__ == "__main__":
    unittest.main()
