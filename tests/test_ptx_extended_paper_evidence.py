"""Actual BMM/Linear packets and coherently rehashed false-evidence controls."""

from contextlib import contextmanager
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import tarfile
import tempfile
import unittest

from reproduction.paper_results.check_snapshot_controls import (
    BMM_CONTROLS, LINEAR_CONTROLS, mutate_bmm_evidence, mutate_linear_evidence,
)
from reproduction.paper_results.ptx_extended_evidence import (
    CONFIG_KEYS, PROTOCOLS, ROOT, check_ptx_extended_evidence, check_recording_packet,
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


class Fixture:
    def __init__(self, root, kind):
        self.root, self.kind, self.protocol = root, kind, PROTOCOLS[kind]
        self.packet = root / self.protocol["prefix"]
        prefixes = [self.protocol[k] for k in ("prefix", "publication_prefix", "ci_prefix", "main_prefix")]
        if kind == "linear":
            prefixes.append(PROTOCOLS["bmm"]["main_prefix"])
        for prefix in prefixes:
            shutil.copytree(ROOT / prefix, root / prefix)
        declared = [p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()]
        self.config = {CONFIG_KEYS[kind]: {k: self.protocol[k] for k in (
            "prefix", "publication_prefix", "ci_prefix", "main_prefix")},
            "evidence_groups": {kind: declared}}

    def manifest(self, prefix):
        root = self.root / prefix
        (root / "manifest.json").write_bytes(encoded({p.name: sha(p.read_bytes())
            for p in sorted(root.iterdir()) if p.is_file() and p.name != "manifest.json"}))

    def report(self, mutate):
        path = self.packet / "results.json"
        value = read(path)
        mutate(value)
        path.write_bytes(encoded(value))
        self.manifest(self.protocol["prefix"])

    def auxiliary(self, prefix, name, mutate):
        path = self.root / prefix / name
        value = read(path)
        mutate(value)
        path.write_bytes(encoded(value))
        self.manifest(prefix)

    def archive(self, label, mutate, *, copied_summary=None):
        path = self.packet / (label + ".tar.gz")
        with tarfile.open(path, mode="r|gz") as archive:
            entries = {m.name: archive.extractfile(m).read() for m in archive}
        mutate(entries)
        manifests = [n for n in entries if n == "manifest.json" or n.endswith("/manifest.json")]
        for name in sorted(manifests, key=lambda n: n.count("/"), reverse=True):
            prefix = name.removesuffix("manifest.json")
            entries[name] = encoded({n[len(prefix):]: sha(data) for n, data in sorted(entries.items())
                                     if n.startswith(prefix) and n != name})
        with path.open("wb") as raw, \
                gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0, compresslevel=1) as compressed, \
                tarfile.open(fileobj=compressed, mode="w") as archive:
            for name, data in sorted(entries.items()):
                member = tarfile.TarInfo(name)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        inventory = self.packet / (label + "-files.json")
        inventory.write_bytes(encoded({n: sha(data) for n, data in sorted(entries.items())}))
        if copied_summary:
            (self.packet / copied_summary).write_bytes(entries["results.json"])
        self.report(lambda report: report["archives"][label].update(
            files=len(entries), uncompressed_bytes=sum(map(len, entries.values())), archive_bytes=path.stat().st_size,
            archive_sha256=sha(path.read_bytes()), inventory_sha256=sha(inventory.read_bytes())))

    def check(self, *, whole=False):
        if whole:
            return check_ptx_extended_evidence(self.config, kind=self.kind, root=self.root)
        return check_recording_packet(self.packet, kind=self.kind)


@contextmanager
def fixture(kind):
    with tempfile.TemporaryDirectory(prefix="lark-extended-ptx-evidence-") as temporary:
        yield Fixture(Path(temporary), kind)


class ExtendedPtxEvidenceTests(unittest.TestCase):
    def test_actual_complete_packets_publication_ci_and_main_without_git(self):
        for kind, members, positives, jobs in (("bmm", 702, 5, 22), ("linear", 960, 4, 23)):
            with self.subTest(kind=kind), fixture(kind) as evidence:
                result = evidence.check(whole=True)
                self.assertEqual(result["independent_source_bound_development_proofs"], 1)
                self.assertEqual(result["retained_positive_Main_checks"], positives)
                self.assertEqual(result["archive_members_checked"], members)
                self.assertEqual(result["successful_source_CI_jobs"], jobs)
                self.assertFalse(result["fresh_experiments_by_ledger"])
                self.assertFalse(result["nvidia_execution"])
                self.assertFalse(result["original_paper_fully_reproduced"])
                self.assertFalse((evidence.root / ".git").exists())

    def test_all_sixteen_rehashed_scope_controls_reach_the_semantic_gate(self):
        for kind, controls, mutate in (("bmm", BMM_CONTROLS, mutate_bmm_evidence),
                                       ("linear", LINEAR_CONTROLS, mutate_linear_evidence)):
            with fixture(kind) as evidence:
                baseline = {name: (evidence.root / name).read_bytes()
                            for name in evidence.config["evidence_groups"][kind]}
                for control, gate in controls:
                    with self.subTest(control=control):
                        changed = baseline.copy()
                        mutate(changed, evidence.config, control)
                        paths = [n for n in changed if changed[n] is not baseline[n]]
                        self.assertEqual(len(paths), 2)
                        try:
                            for name in paths:
                                (evidence.root / name).write_bytes(changed[name])
                            with self.assertRaisesRegex(ValueError, "PTX " + kind + " " + gate):
                                evidence.check(whole=True)
                        finally:
                            for name in paths:
                                (evidence.root / name).write_bytes(baseline[name])

    def test_failed_and_partial_checks_cannot_add_official_successes(self):
        for kind, field in (("bmm", "retained_positive_Main_checks"),
                            ("linear", "retained_positive_Main_checks")):
            with self.subTest(kind=kind), fixture(kind) as evidence:
                evidence.report(lambda r: r.update({field: r[field] + 1}))
                with self.assertRaisesRegex(ValueError, "kernel/recheck/execution counters differ"):
                    evidence.check()

    def test_bmm_failed_official_export_cannot_be_relabeled_as_accepted(self):
        with fixture("bmm") as evidence:
            def mutate(entries):
                proof = json.loads(entries["results.json"])
                proof.update(status="verified-source-bound-full-PTX-BMM", source_bound_proof_accepted=True,
                             source_bound_development_proofs=1)
                entries["results.json"] = encoded(proof)
            evidence.archive("failed-export-v2", mutate, copied_summary="failed-export-results.json")
            with self.assertRaisesRegex(ValueError, "positive source/contract/proof binding differs"):
                evidence.check()

    def test_missing_raw_history_member_refused_even_with_updated_all_outer_hashes(self):
        with fixture("bmm") as evidence:
            evidence.archive("development-history", lambda entries: entries.pop(next(iter(entries))))
            with self.assertRaisesRegex(ValueError, "archive size/inventory differs"):
                evidence.check()

    def test_rehashed_history_annotation_cannot_erase_the_failed_cold_driver(self):
        with fixture("linear") as evidence:
            path = evidence.packet / "validation-history.json"
            history = read(path)
            history["earlier_actual_terminal_exit_codes"]["initialization-cold-v1"] = 0
            path.write_bytes(encoded(history))
            evidence.manifest(evidence.protocol["prefix"])
            with self.assertRaisesRegex(ValueError, "retained development history differs"):
                evidence.check()

    def test_positive_replay_cannot_claim_cached_owned_imports(self):
        for kind in PROTOCOLS:
            with self.subTest(kind=kind), fixture(kind) as evidence:
                def mutate(entries):
                    proof = json.loads(entries["results.json"])
                    proof["old_owned_olean_cache_used"] = True
                    entries["results.json"] = encoded(proof)
                evidence.archive("replay", mutate)
                with self.assertRaisesRegex(ValueError, "positive source/contract/proof binding differs"):
                    evidence.check()

    def test_edited_accepted_log_and_matching_audit_cannot_add_custom_axiom(self):
        for kind in PROTOCOLS:
            with self.subTest(kind=kind), fixture(kind) as evidence:
                def mutate(entries):
                    proof = json.loads(entries["results.json"])
                    tag = evidence.protocol["certificate_namespace"] + ".kernel_eq_spec"
                    proof["axiom_audits"][tag].append("custom_axiom")
                    entries["Main.log"] = entries["Main.log"].replace(
                        ("'" + tag + "' depends on axioms: [propext, Classical.choice, Quot.sound]").encode(),
                        ("'" + tag + "' depends on axioms: [propext, Classical.choice, Quot.sound, custom_axiom]").encode())
                    proof["main_check"]["log_sha256"] = sha(entries["Main.log"])
                    entries["results.json"] = encoded(proof)
                evidence.archive("export", mutate, copied_summary="proof-results.json")
                with self.assertRaisesRegex(ValueError, "positive axiom audit differs"):
                    evidence.check()

    def test_linear_bias_cannot_be_added_after_final_half_conversion(self):
        with fixture("linear") as evidence:
            def mutate(entries):
                tree = json.loads(entries["reference-ast.json"])
                tree = ["add", ["toHalf", tree[1][1]], tree[1][2]]
                entries["reference-ast.json"] = encoded(tree)
                proof = json.loads(entries["results.json"])
                proof["reference_ast_sha256"] = sha(entries["reference-ast.json"])
                entries["results.json"] = encoded(proof)
            evidence.archive("export", mutate, copied_summary="proof-results.json")
            with self.assertRaisesRegex(ValueError, "positive reference AST differs"):
                evidence.check()

    def test_boolean_reference_buffer_is_not_numeric_zero(self):
        with fixture("bmm") as evidence:
            def mutate(entries):
                tree = json.loads(entries["reference-ast.json"])
                tree[1][1][1][1] = False
                entries["reference-ast.json"] = encoded(tree)
                proof = json.loads(entries["results.json"])
                proof["reference_ast_sha256"] = sha(entries["reference-ast.json"])
                entries["results.json"] = encoded(proof)
            evidence.archive("export", mutate)
            with self.assertRaisesRegex(ValueError, "positive reference AST differs"):
                evidence.check()

    def test_duplicated_module_name_is_not_a_complete_owned_build(self):
        with fixture("linear") as evidence:
            def mutate(entries):
                proof = json.loads(entries["results.json"])
                proof["module_checks"][-1]["module"] = proof["module_checks"][-2]["module"]
                entries["results.json"] = encoded(proof)
            evidence.archive("export", mutate)
            with self.assertRaisesRegex(ValueError, "positive module roster differs"):
                evidence.check()

    def test_bool_success_code_and_increased_timeout_are_not_bounded_successes(self):
        for field, value in (("exit_code", False), ("timeout_seconds", 181)):
            with self.subTest(field=field), fixture("bmm") as evidence:
                def mutate(entries):
                    proof = json.loads(entries["results.json"])
                    proof["main_check"][field] = value
                    entries["results.json"] = encoded(proof)
                evidence.archive("export", mutate)
                with self.assertRaisesRegex(ValueError, "recorded checker completion/budget/log differs"):
                    evidence.check()

    def test_direct_negative_error_must_reach_actual_source_program(self):
        with fixture("linear") as evidence:
            def mutate(entries):
                report = json.loads(entries["results.json"])
                control = report["negative_controls"][0]
                base = control["control"] + "/"
                original = entries[base + "Main.log"]
                entries[base + "Main.log"] = re.sub(
                    rb"(Main\.lean:)[0-9]+(:[0-9]+: error:)", rb"\g<1>999\2", original, count=1)
                self.assertNotEqual(entries[base + "Main.log"], original)
                control["Lean"]["log_sha256"] = sha(entries[base + "Main.log"])
                entries[base + "results.json"] = encoded(control)
                entries["results.json"] = encoded(report)
            evidence.archive("controls", mutate, copied_summary="controls-results.json")
            with self.assertRaisesRegex(ValueError, "direct Lean binding-control refusal differs"):
                evidence.check()

    def test_installed_package_cannot_import_checkout_or_relax_legacy_pins(self):
        for kind, field, value in (("bmm", "checkout_imported", True),
                                   ("linear", "legacy_BMM60_source_bytes_and_Main_unchanged", False)):
            with self.subTest(kind=kind), fixture(kind) as evidence:
                def mutate(entries):
                    installed = json.loads(entries["results.json"])
                    installed[field] = value
                    entries["results.json"] = encoded(installed)
                evidence.archive("installed-wheel", mutate, copied_summary="installed-wheel-results.json")
                with self.assertRaisesRegex(ValueError, "installed-wheel replay differs"):
                    evidence.check()

    def test_publication_requires_successful_anonymous_tls_observation(self):
        with fixture("linear") as evidence:
            evidence.auxiliary(evidence.protocol["publication_prefix"], "results.json",
                               lambda r: r.update(tls_verification=False))
            with self.assertRaisesRegex(ValueError, "anonymous publication scope differs"):
                evidence.check(whole=True)

    def test_missing_main_receipt_cannot_satisfy_final_ledger(self):
        with fixture("bmm") as evidence:
            (evidence.root / evidence.protocol["main_prefix"] / "results.json").unlink()
            with self.assertRaisesRegex(ValueError, "auxiliary inventory differs"):
                evidence.check(whole=True)

    def test_main_promotion_rejects_force_push_even_after_receipt_rehash(self):
        with fixture("linear") as evidence:
            evidence.auxiliary(evidence.protocol["main_prefix"], "update.json",
                               lambda r: r.update(force=True))
            with self.assertRaisesRegex(ValueError, "main promotion guard/update differs"):
                evidence.check(whole=True)


if __name__ == "__main__":
    unittest.main()
