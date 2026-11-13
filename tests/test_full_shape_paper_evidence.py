"""Semantic mutations of the actual five-cohort frozen model evidence."""

import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from reproduction.paper_results.full_shape_evidence import check_full_shape_evidence
from reproduction.paper_results.prepare_full_shape_snapshot import augment_auditor, prepare_snapshot


ROOT = Path(__file__).resolve().parents[1]
BASE = "reproduction/local_models/results"
COMPARISON = BASE + "/full-shape-comparison-five-cohorts-v1"
NAMES = ("results.json", "raw-results.json", "audit-results.json", "binding.json",
         "cohort-files.json", "audit-files.json", "manifest.json")


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class FullShapePaperEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lark-model-ledger-controls-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        report = read(ROOT / COMPARISON / "results.json")
        paths = [COMPARISON + "/" + name for name in
                 ("results.json", "binding.json", "RESULTS.md", "manifest.json")]
        paths.append("reproduction/local_models/compare_full_shape.py")
        packets = []
        for row in report["inputs"]:
            prefix = BASE + "/" + row["packet_id"]
            packets.append({"prefix": prefix, "manifest_sha256": row["packet_manifest_sha256"]})
            paths += [prefix + "/" + name for name in NAMES]
        self.config = {"evidence_groups": {"full_shape_models": paths},
                       "full_shape_models": {"comparison_prefix": COMPARISON,
                                             "required_cohorts": 5, "packets": packets}}
        for name in paths:
            destination = self.root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, destination)

    def record(self, prefix, name):
        return read(self.root / prefix / name)

    def update(self, prefix, name, mutate):
        path = self.root / prefix / name
        value = read(path)
        mutate(value)
        write(path, value)

    def rehash(self):
        """Synchronize report hashes and the configuration's packet pins."""
        report = self.record(COMPARISON, "results.json")
        binding = self.record(COMPARISON, "binding.json")
        for expected, row, bound in zip(self.config["full_shape_models"]["packets"],
                                        report["inputs"], binding["inputs"], strict=True):
            packet = self.root / expected["prefix"]
            audit, proof = read(packet / "audit-results.json"), read(packet / "binding.json")
            audit["recording_results_sha256"] = sha(packet / "raw-results.json")
            write(packet / "audit-results.json", audit)
            proof["raw_results_sha256"] = sha(packet / "raw-results.json")
            proof["audit_results_sha256"] = sha(packet / "audit-results.json")
            write(packet / "binding.json", proof)
            manifest = read(packet / "manifest.json")
            for name in NAMES:
                if name != "manifest.json":
                    manifest[name] = sha(packet / name)
            write(packet / "manifest.json", manifest)
            digest = sha(packet / "manifest.json")
            expected["manifest_sha256"] = row["packet_manifest_sha256"] = bound["manifest_sha256"] = digest
        write(self.root / COMPARISON / "results.json", report)
        write(self.root / COMPARISON / "binding.json", binding)
        manifest = self.record(COMPARISON, "manifest.json")
        for name in manifest:
            manifest[name] = sha(self.root / COMPARISON / name)
        write(self.root / COMPARISON / "manifest.json", manifest)

    def refused(self, gate):
        self.rehash()
        with self.assertRaisesRegex(ValueError, gate):
            check_full_shape_evidence(self.config, root=self.root)

    def test_actual_five_cohorts_without_git_sdk_or_raw_archives(self):
        report = check_full_shape_evidence(self.config, root=self.root)
        self.assertEqual(report["complete_independent_cohorts"], 5)
        self.assertEqual(sum(row["counts"]["verified_within_budget"] for row in report["cohorts"]), 69)
        self.assertEqual(sum(row["counts"]["model_requests"] for row in report["cohorts"]), 659)
        self.assertEqual(report["all_task_reported_usage"]["total_tokens"], 13247377)
        self.assertEqual(report["missing_independent_cohorts"],
                         [{"model": "zai-org/GLM-5.3", "source_language": "cuda"}])
        self.assertIs(report["all_six_independent_cohorts_present"], False)
        self.assertIs(report["original_paper_fully_reproduced"], False)
        self.assertIs(report["fresh_experiments_by_ledger"], False)
        self.assertFalse((self.root / ".git").exists())
        self.assertFalse(any(self.root.rglob("*.tar.gz")))

    def test_five_cannot_satisfy_six_required_cohorts(self):
        self.config["full_shape_models"]["required_cohorts"] = 6
        self.refused("declared cohort count differs")

    def test_snapshot_builder_refuses_actual_five_before_creating_output(self):
        snapshot = self.root / "must-not-be-created"
        with self.assertRaisesRegex(ValueError, "All six complete independent cohorts are required"):
            prepare_snapshot(evidence_commit="0" * 40, comparison_prefix=COMPARISON,
                             source_archive=self.root / "must-not-be-read",
                             snapshot=snapshot, root=self.root)
        self.assertFalse(snapshot.exists())

    def test_augmented_frozen_auditor_renders_actual_recorded_models(self):
        source = (ROOT / "reproduction/paper_results/snapshots/20261112-v22/auditor.py").read_text()
        draft = augment_auditor(source)
        namespace = {"__name__": "isolated_model_ledger_renderer",
                     "__file__": str(ROOT / "reproduction/paper_results/audit.py")}
        exec(compile(draft, "frozen-model-ledger-auditor.py", "exec"), namespace)
        report = read(ROOT / "reproduction/paper_results/snapshots/20261112-v22/results/audit.json")
        report["full_shape_model_evidence_checks"] = check_full_shape_evidence(self.config, root=self.root)
        report["evidence_groups"]["full_shape_models"] = [COMPARISON + "/RESULTS.md"]
        linked = [COMPARISON + "/RESULTS.md",
                  "reproduction/paper_results/original-artifact-full-query-20261112/results.json",
                  "reproduction/paper_results/original-artifact-refresh-20261113-0900/results.json",
                  "reproduction/local_models/results/ptx-verifier-implementation-review-v1/results.json"]
        for name in linked:
            report["evidence_links"][name] = "https://github.com/harsh-nod/lark/blob/253f40923cafcaeb23829e4f1f1322fc59302efd/" + name
        rendered = namespace["render"](report, self.root).decode()
        self.assertIn("5 complete independent model/language cohorts, 69 verified proofs and 659 recorded responses.", rendered)
        lines = rendered.splitlines()
        header = next(i for i, line in enumerate(lines) if line.startswith("| Paper item / source label |"))
        self.assertTrue(lines[header + 1].startswith("| ---"))
        self.assertTrue(lines[header + 2].startswith("| "))
        self.assertIn("original paper is not fully reproduced", rendered)

    def test_global_original_result_overclaim(self):
        self.update(COMPARISON, "results.json", lambda value: value.update(original_paper_fully_reproduced=True))
        self.refused("comparison execution/original scope differs")

    def test_false_complete_six_roster(self):
        self.update(COMPARISON, "results.json", lambda value: value.update(
            all_six_independent_cohorts_present=True, missing_cohorts=[]))
        self.refused("complete/missing cohort roster differs")

    def test_changed_source_revision(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "results.json", lambda value: value.update(revision="0" * 40))
        self.refused("model/language/revision identity differs")

    def test_stub_cohort(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "results.json", lambda value: value.update(test_stub=True))
        self.refused("complete non-stub fixed protocol differs")

    def test_case_only_stub_marker(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "raw-results.json", lambda value: value["cases"][0].update(test_stub=True))
        self.refused("case stub/execution scope differs")

    def test_partial_audit_selected_case_roster(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "audit-results.json", lambda value: value.update(selected_cases=["relu"]))
        self.refused("case roster/summary differs")

    def test_new_registered_certificate_claim(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "results.json", lambda value: value.update(new_registered_source_certificates=1))
        self.refused("cohort execution/original scope differs")

    def test_first_response_relabelled_as_first_lean_check(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        summary = self.record(packet, "results.json")
        summary["cases"][0]["first_response_verified"] = True
        write(self.root / packet / "results.json", summary)
        self.update(COMPARISON, "results.json", lambda value: value["inputs"][0].update(cases=summary["cases"]))
        self.refused("case counters/first-attempt metrics differ")

    def test_boolean_request_count(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "results.json", lambda value: value["counts"].update(first_response_verified=False))
        self.update(COMPARISON, "results.json", lambda value: value["inputs"][0]["recorded_counts"].update(first_response_verified=False))
        self.refused("cohort/replay counters differ")

    def test_fresh_accepted_main_hash_changed(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        audit = self.record(packet, "audit-results.json")
        name = audit["fresh_accepted_proof_kernel_checks"][0] + "/Main.lean"
        self.update(packet, "audit-files.json", lambda value: value.update({name: "0" * 64}))
        self.refused("recorded accepted-Main replay binding differs")

    def test_failed_candidates_claimed_freshly_rechecked(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        self.update(packet, "binding.json", lambda value: value.update(failed_lean_candidates_freshly_rechecked=True))
        self.refused("recorded proof/protocol binding differs")

    def test_success_only_mean_denominator_changed(self):
        def mutate(value):
            value["inputs"][0]["levels"]["level1"]["mean_denominator_verified_tasks"] = 12
        self.update(COMPARISON, "results.json", mutate)
        self.refused("successful-task token means/denominators differ")

    def test_case_usage_cannot_disagree_with_cohort_totals(self):
        packet = self.config["full_shape_models"]["packets"][0]["prefix"]
        summary = self.record(packet, "results.json")
        summary["cases"][0]["reported_usage"]["prompt_tokens"] += 1
        summary["cases"][0]["reported_usage"]["total_tokens"] += 1
        write(self.root / packet / "results.json", summary)
        self.update(COMPARISON, "results.json", lambda value: value["inputs"][0].update(cases=summary["cases"]))
        self.refused("cohort usage reconciliation differs")

    def test_failed_case_cannot_stop_before_its_budget(self):
        packet = BASE + "/full-shape-cohort-glm53-hip-v1"
        def mutate(value):
            case = next(row for row in value["cases"] if row["case"] == "rmsnorm")
            self.assertEqual(case["calls"][-1]["status"], "unproved")
            case["calls"].pop()
            case["proof_checks"] -= 1
        self.update(packet, "raw-results.json", mutate)
        self.refused("case completion/budget differs")


if __name__ == "__main__":
    unittest.main()
