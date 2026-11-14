"""Check standalone replay and fully rehashed false-completion controls."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import uuid

if __package__:
    from .replay_snapshot import DEFAULT, file_set, read, write
else:
    from replay_snapshot import DEFAULT, file_set, read, write


# Temporary false-control archives preserve member bytes at faster compression.
CONTROL_COMPRESSION_LEVEL = 1


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rehash(snapshot, *, archive_changed=False):
    if archive_changed:
        provenance = read(snapshot / "provenance.json")
        if provenance["schema"] == 2:
            provenance["evidence_layout_sha256"] = sha(snapshot / "evidence-layout.json")
        else:
            provenance["evidence_archive_sha256"] = sha(snapshot / "evidence.tar.gz")
        provenance["evidence_manifest_sha256"] = sha(snapshot / "evidence-manifest.json")
        write(snapshot / "provenance.json", provenance)
    results = snapshot / "results"
    write(results / "manifest.json", {n: sha(results / n) for n in ("audit.json", "RESULTS.md")})
    write(
        snapshot / "manifest.json",
        {n: sha(snapshot / n) for n in sorted(file_set(snapshot)) if n != "manifest.json"},
    )


MODEL_CONTROLS = (
    ("model-declared-cohort-count", "declared cohort count differs"),
    ("model-false-missing-roster", "complete/missing cohort roster differs"),
    ("model-original-result-overclaim", "comparison execution/original scope differs"),
    ("model-changed-checkpoint-revision", "model/language/revision identity differs"),
    ("model-stub-cohort", "complete non-stub fixed protocol differs"),
    ("model-partial-audit-roster", "case roster/summary differs"),
    ("model-case-only-stub", "case stub/execution scope differs"),
    ("model-source-certificate-overclaim", "cohort execution/original scope differs"),
    ("model-first-response-relabeled", "case counters/first-attempt metrics differ"),
    ("model-boolean-numeric-counter", "cohort/replay counters differ"),
    ("model-mismatched-accepted-Main", "recorded accepted-Main replay binding differs"),
    ("model-failed-candidates-falsely-rechecked", "recorded proof/protocol binding differs"),
    ("model-mean-denominator-changed", "successful-task token means/denominators differ"),
    ("model-case-cost-reconciliation", "cohort usage reconciliation differs"),
    ("model-premature-failed-case-stop", "case completion/budget differs"),
    ("model-context-budget-increased", "comparison roster/protocol differs"),
    ("model-forged-extra-fresh-check", "cohort/replay counters differ"),
)

PTX_CONTROLS = (
    ("ptx-rechecks-counted-as-kernels", "kernel/recheck/execution counters differ"),
    ("ptx-boolean-kernel-counter", "kernel/recheck/execution counters differ"),
    ("ptx-original-result-overclaim", "proof contract/original scope differs"),
    ("ptx-nvidia-execution-overclaim", "proof contract/original scope differs"),
    ("ptx-proof-budget-increased", "proof contract/original scope differs"),
    ("ptx-launch-geometry-changed", "proof contract/original scope differs"),
    ("ptx-CUDA-contract-fuel-changed", "proof contract/original scope differs"),
    ("ptx-source-CI-wrong-commit", "actual source CI differs"),
)

GEMV_CONTROLS = tuple(("gemv" + name.removeprefix("ptx"), gate) for name, gate in PTX_CONTROLS)
GEMM_CONTROLS = tuple(("gemm" + name.removeprefix("ptx"), gate) for name, gate in PTX_CONTROLS)
BMM_CONTROLS = tuple(("bmm" + name.removeprefix("ptx"), gate) for name, gate in PTX_CONTROLS)
LINEAR_CONTROLS = tuple(("linear" + name.removeprefix("ptx"), gate) for name, gate in PTX_CONTROLS)


class ControlArchive:
    """Reuse immutable member bytes while preserving every false snapshot member.

    Concatenated gzip members decode to an ordinary complete tar stream. Each
    worker owns its metadata mutations, output archive and replay; at most two
    replayers run concurrently, with the existing resource limits unchanged.
    """

    def __init__(self, path):
        with tarfile.open(path) as archive:
            self.entries = {member.name: archive.extractfile(member).read() for member in archive}
        self.hashes = {name: hashlib.sha256(data).hexdigest() for name, data in self.entries.items()}
        self.chunks = {name: self.chunk(name, data) for name, data in self.entries.items()}
        self.end = gzip.compress(b"\0" * 1024, compresslevel=CONTROL_COMPRESSION_LEVEL, mtime=0)

    @staticmethod
    def chunk(name, data):
        info = tarfile.TarInfo(name)
        info.size = len(data)
        payload = info.tobuf(format=tarfile.PAX_FORMAT) + data + b"\0" * ((-len(data)) % 512)
        return gzip.compress(payload, compresslevel=CONTROL_COMPRESSION_LEVEL, mtime=0)

    def write(self, snapshot, entries):
        hashes = {}
        with (snapshot / "evidence.tar.gz").open("wb") as output:
            for name, data in entries.items():
                if name in self.entries and data is self.entries[name]:
                    output.write(self.chunks[name])
                    hashes[name] = self.hashes[name]
                else:
                    output.write(self.chunk(name, data))
                    hashes[name] = hashlib.sha256(data).hexdigest()
            output.write(self.end)
        write(snapshot / "evidence-manifest.json", hashes)


def control_archive(snapshot):
    if read(snapshot / "provenance.json")["schema"] == 2:
        if __package__:
            from .snapshot_control_archives import ChunkedControlArchive
        else:
            from snapshot_control_archives import ChunkedControlArchive
        return ChunkedControlArchive(snapshot)
    return ControlArchive(snapshot / "evidence.tar.gz")


def mutate_gemv_evidence(entries, config, control):
    """Apply the same complete metadata controls to the separate GEMV packet."""
    selected = {**config, "ptx_pointwise_proof": config["ptx_dot_proof"]}
    mutate_ptx_evidence(entries, selected, "ptx" + control.removeprefix("gemv"))


def mutate_gemm_evidence(entries, config, control):
    """Preserve the complete GEMM packet while synchronizing false metadata."""
    selected = {**config, "ptx_pointwise_proof": config["ptx_matrix_proof"]}
    mutate_ptx_evidence(entries, selected, "ptx" + control.removeprefix("gemm"))


def mutate_bmm_evidence(entries, config, control):
    """Preserve every BMM recording while changing the selected scope claim."""
    selected = {**config, "ptx_pointwise_proof": config["ptx_batched_proof"]}
    mutate_ptx_evidence(entries, selected, "ptx" + control.removeprefix("bmm"))


def mutate_linear_evidence(entries, config, control):
    """Preserve every Linear recording while changing the selected scope claim."""
    selected = {**config, "ptx_pointwise_proof": config["ptx_linear_proof"]}
    mutate_ptx_evidence(entries, selected, "ptx" + control.removeprefix("linear"))


def mutate_ptx_evidence(entries, config, control):
    """Change actual copied proof metadata and synchronize its packet manifest."""
    spec = config["ptx_pointwise_proof"]
    prefix = spec["ci_prefix"] if control == "ptx-source-CI-wrong-commit" else spec["prefix"]
    name = "run.json" if control == "ptx-source-CI-wrong-commit" else "results.json"
    record = json.loads(entries[prefix + "/" + name])
    if control == "ptx-rechecks-counted-as-kernels":
        record["independent_source_bound_development_proofs"] = 4
    elif control == "ptx-boolean-kernel-counter":
        record["independent_source_bound_development_proofs"] = True
    elif control == "ptx-original-result-overclaim":
        record["original_paper_fully_reproduced"] = True
    elif control == "ptx-nvidia-execution-overclaim":
        record["nvidia_execution"] = True
    elif control == "ptx-proof-budget-increased":
        record["limits"]["maxHeartbeats"] += 1
    elif control == "ptx-launch-geometry-changed":
        record["launch"]["block"] = 32
    elif control == "ptx-CUDA-contract-fuel-changed":
        record["unchanged_CUDA_contract_fuel"][0] = 15
    elif control == "ptx-source-CI-wrong-commit":
        record["head_sha"] = "0" * 40
    else:
        raise ValueError("Unknown PTX control: " + control)
    entries[prefix + "/" + name] = (json.dumps(record, indent=2) + "\n").encode()
    manifest = json.loads(entries[prefix + "/manifest.json"])
    for member in manifest:
        manifest[member] = hashlib.sha256(entries[prefix + "/" + member]).hexdigest()
    entries[prefix + "/manifest.json"] = (json.dumps(manifest, indent=2) + "\n").encode()


def mutate_model_evidence(entries, config, control):
    """Change copied metadata and synchronize every inner report/pin binding."""
    def get(name):
        return json.loads(entries[name])

    def put(name, value):
        entries[name] = (json.dumps(value, indent=2) + "\n").encode()

    def digest(name):
        return hashlib.sha256(entries[name]).hexdigest()

    spec = config["full_shape_models"]
    comparison = spec["comparison_prefix"]
    report, bound = get(comparison + "/results.json"), get(comparison + "/binding.json")
    if control == "model-declared-cohort-count":
        spec["required_cohorts"] -= 1
    elif control == "model-false-missing-roster":
        report["missing_cohorts"] = [{"model": "zai-org/GLM-5.3", "source_language": "hip"}]
    elif control == "model-original-result-overclaim":
        report["original_paper_fully_reproduced"] = True
    elif control == "model-context-budget-increased":
        report["protocol"]["context_limit"] += 1
        for item in spec["packets"]:
            for name in ("results.json", "raw-results.json"):
                path = item["prefix"] + "/" + name
                data = get(path)
                data["protocol"] = dict(report["protocol"])
                put(path, data)
    else:
        index = 0
        if control == "model-premature-failed-case-stop":
            index = next(i for i, item in enumerate(spec["packets"])
                         if any(case["status"] == "budget-exhausted"
                                for case in get(item["prefix"] + "/raw-results.json")["cases"]))
        packet = spec["packets"][index]["prefix"]
        summary, raw, audit, proof = (get(packet + "/" + name) for name in
                                     ("results.json", "raw-results.json", "audit-results.json", "binding.json"))
        row = report["inputs"][index]
        if control == "model-changed-checkpoint-revision":
            summary["revision"] = "0" * 40
        elif control == "model-stub-cohort":
            summary["test_stub"] = True
        elif control == "model-partial-audit-roster":
            audit["selected_cases"] = [raw["cases"][0]["case"]]
        elif control == "model-case-only-stub":
            raw["cases"][0]["test_stub"] = True
        elif control == "model-source-certificate-overclaim":
            summary["new_registered_source_certificates"] = 1
        elif control == "model-first-response-relabeled":
            case = summary["cases"][0]
            case["first_response_verified"] = not case["first_response_verified"]
            row["cases"] = summary["cases"]
        elif control == "model-boolean-numeric-counter":
            summary["counts"]["first_response_verified"] = bool(summary["counts"]["first_response_verified"])
            row["recorded_counts"] = summary["counts"]
        elif control == "model-mismatched-accepted-Main":
            inventory = get(packet + "/audit-files.json")
            inventory[audit["fresh_accepted_proof_kernel_checks"][0] + "/Main.lean"] = "0" * 64
            put(packet + "/audit-files.json", inventory)
        elif control == "model-failed-candidates-falsely-rechecked":
            proof["failed_lean_candidates_freshly_rechecked"] = True
        elif control == "model-mean-denominator-changed":
            row["levels"]["level1"]["mean_denominator_verified_tasks"] += 1
        elif control == "model-case-cost-reconciliation":
            summary["cases"][0]["reported_usage"]["prompt_tokens"] += 1
            summary["cases"][0]["reported_usage"]["total_tokens"] += 1
            row["cases"] = summary["cases"]
        elif control == "model-premature-failed-case-stop":
            case = next(case for case in raw["cases"] if case["status"] == "budget-exhausted")
            case["calls"].pop()
            case["proof_checks"] = sum(call["status"] in ("unproved", "verified-proof") for call in case["calls"])
            case["library_reads"] = sum(call["status"] == "library-read" for call in case["calls"])
        elif control == "model-forged-extra-fresh-check":
            summary["counts"]["additional_fresh_kernel_checks"] += 1
            row["recorded_counts"] = summary["counts"]
        else:
            raise ValueError("Unknown model control: " + control)
        for name, value in (("results.json", summary), ("raw-results.json", raw),
                            ("audit-results.json", audit), ("binding.json", proof)):
            put(packet + "/" + name, value)
    names = ("results.json", "raw-results.json", "audit-results.json", "binding.json",
             "cohort-files.json", "audit-files.json")
    for expected, row, binding in zip(spec["packets"], report["inputs"], bound["inputs"], strict=True):
        packet = expected["prefix"]
        audit, proof = get(packet + "/audit-results.json"), get(packet + "/binding.json")
        audit["recording_results_sha256"] = digest(packet + "/raw-results.json")
        put(packet + "/audit-results.json", audit)
        proof["raw_results_sha256"] = digest(packet + "/raw-results.json")
        proof["audit_results_sha256"] = digest(packet + "/audit-results.json")
        put(packet + "/binding.json", proof)
        manifest = get(packet + "/manifest.json")
        for name in names:
            manifest[name] = digest(packet + "/" + name)
        put(packet + "/manifest.json", manifest)
        value = digest(packet + "/manifest.json")
        expected["manifest_sha256"] = row["packet_manifest_sha256"] = binding["manifest_sha256"] = value
    put(comparison + "/results.json", report)
    put(comparison + "/binding.json", bound)
    manifest = get(comparison + "/manifest.json")
    for name in manifest:
        manifest[name] = digest(comparison + "/" + name)
    put(comparison + "/manifest.json", manifest)
    put("reproduction/paper_results/targets.json", config)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT)
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    snapshot, manuscript, out = (
        args.snapshot.resolve(),
        args.source_archive.resolve(),
        args.output.resolve(),
    )
    out.mkdir(parents=True, exist_ok=False)
    results = []
    with tempfile.TemporaryDirectory(prefix="lark-snapshot-controls-") as temporary:
        root = Path(temporary)
        write(out / "temporary-location.json", {"root": str(root), "pid": os.getpid()})
        script = root / "isolated/bin/replay_snapshot.py"
        script.parent.mkdir(parents=True)
        shutil.copyfile(Path(__file__).with_name("replay_snapshot.py"), script)
        if read(snapshot / "provenance.json")["schema"] == 2:
            shutil.copyfile(Path(__file__).with_name("snapshot_archives.py"),
                            script.with_name("snapshot_archives.py"))
        isolated = root / "isolated/snapshot"
        shutil.copytree(snapshot, isolated)
        packed_controls = control_archive(snapshot)
        env = dict(os.environ)
        env["PATH"] = "/nonexistent"
        env.pop("PYTHONPATH", None)
        env["PYTHONNOUSERSITE"] = "1"

        def execute(name, data, source=manuscript):
            run = subprocess.run(
                [
                    sys.executable,
                    str(script),
                    "--snapshot",
                    str(data),
                    "--source-archive",
                    str(source),
                ],
                cwd=root / "isolated",
                env=env,
                capture_output=True,
                text=True,
                timeout=120,
            )
            log = run.stdout + run.stderr
            (out / (name + ".log")).write_text(log)
            return run.returncode, log

        code, log = execute("outside-checkout-no-git", isolated)
        if code or "frozen-snapshot-replayed" not in log:
            raise RuntimeError("Standalone replay failed: " + log)
        results.append({"name": "outside-checkout-no-git", "accepted": True, "git_on_path": False})
        names = ["global-completion-claim", "original-production-claim"]
        has_production_cases = "production_cases" in read(snapshot / "targets.json")
        awq_case = next((row for row in read(snapshot / "targets.json").get("production_cases", [])
                         if row["paper_case"] == "vllm-awq-gemm"), None)
        if has_production_cases:
            names.append("false-native-awq-certificate-count" if awq_case["registered_source_certificates"]
                         else "invented-native-awq-coverage")
        for name in names:
            altered = root / name
            shutil.copytree(snapshot, altered)
            report = read(altered / "results/audit.json")
            if name == "global-completion-claim":
                report["original_paper_fully_reproduced"] = True
                report["completion_percentage"] = 100
            elif name == "original-production-claim":
                row = next(r for r in report["floats"] if r["label"] == "tab:lib-kernels")
                row["original_result_reproduced"] = True
            else:
                row = next(r for r in report["production_cases"]
                           if r["paper_case"] == "vllm-awq-gemm")
                row["independent_status"] = "complete-scoped-proof"
                row["registered_source_certificates"] = (
                    awq_case["registered_source_certificates"] + 1
                    if awq_case["registered_source_certificates"] else 4
                )
            write(altered / "results/audit.json", report)
            rehash(altered)
            code, log = execute(name, altered)
            if code == 0 or "Audit differs: audit.json" not in log:
                raise RuntimeError("False completion was not rejected at regeneration: " + log)
            results.append(
                {
                    "name": name,
                    "accepted": False,
                    "fully_rehashed": True,
                    "gate": "frozen report regeneration",
                }
            )
        if has_production_cases:
            altered = root / "missing-production-case"
            shutil.copytree(snapshot, altered)
            targets = read(altered / "targets.json")
            targets["production_cases"] = [
                row for row in targets["production_cases"]
                if row["paper_case"] != "vllm-awq-gemm"
            ]
            write(altered / "targets.json", targets)
            target_name = "reproduction/paper_results/targets.json"
            entries = packed_controls.entries.copy()
            entries[target_name] = (altered / "targets.json").read_bytes()
            packed_controls.write(altered, entries)
            rehash(altered, archive_changed=True)
            code, log = execute("missing-production-case", altered)
            if code == 0 or "Production case inventory differs from manuscript" not in log:
                raise RuntimeError("Production inventory control failed: " + log)
            results.append({
                "name": "missing-production-case", "accepted": False,
                "fully_rehashed": True, "gate": "actual manuscript production table",
            })
        if "production_proof_checks" in read(snapshot / "targets.json"):
            awq = read(snapshot / "targets.json")["production_proof_checks"]["vllm-awq-gemm"]
            for name, selected, field, value, expected_gate in (
                ("rehashed-study-ieee-overclaim", awq["report"], "ieee_equivalence_proved", True,
                 "New production proof scope differs: vllm-awq-gemm"),
                ("rehashed-study-owned-cache-claim", awq["replay"], "own_lean_compiled_cache_seeded", True,
                 "New production replay scope differs: vllm-awq-gemm"),
            ):
                altered = root / name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                record = json.loads(entries[selected])
                record[field] = value
                entries[selected] = (json.dumps(record, indent=2) + "\n").encode()
                inner_manifest = str(Path(selected).with_name("manifest.json"))
                if inner_manifest in entries:
                    hashes = json.loads(entries[inner_manifest])
                    hashes[Path(selected).name] = hashlib.sha256(entries[selected]).hexdigest()
                    entries[inner_manifest] = (json.dumps(hashes, indent=2) + "\n").encode()
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(name, altered)
                if code == 0 or expected_gate not in log:
                    raise RuntimeError("Study scope control failed: " + name + "\n" + log)
                results.append({
                    "name": name, "accepted": False, "fully_rehashed": True,
                    "gate": "frozen study scope consistency",
                })
        if "numerical_studies" in read(snapshot / "targets.json"):
            production = "reproduction/specification_validation/results/production-real"
            benchmark = "reproduction/benchmark_specification_validation/results/benchmark-float64"
            cases = [
                ("numerical-benchmark-ieee-overclaim", benchmark+"-v1/results.json",
                 ["ieee_equivalence_theorem"], True, "arithmetic/resource scope differs: benchmark"),
                ("numerical-production-ieee-overclaim", production+"-v1/results.json",
                 ["formal_ieee_or_error_theorem"], True, "arithmetic scope differs: production"),
                ("numerical-changed-heartbeat-cap", benchmark+"-v1/results.json",
                 ["maxHeartbeats"], 2000001, "arithmetic/resource scope differs: benchmark"),
                ("numerical-duplicate-case", benchmark+"-v1/results.json",
                 ["checks", 1, "stratum"], "dyadic", "case coverage differs: benchmark"),
                ("numerical-incomplete-score-total", benchmark+"-v1/results.json",
                 ["score_comparison_count"], 589823, "replay/score binding differs: benchmark"),
                ("numerical-score-bit-disagreement", benchmark+"-v1/results.json",
                 ["checks", 60, "score_tensor_comparison", "bit_identical"], 16383,
                 "score coverage differs: benchmark"),
                ("numerical-changed-sampled-value", benchmark+"-v1/results.json",
                 ["checks", 0, "samples", 0, "lean_float64"], 123.0, "sampled value differs: benchmark"),
                ("numerical-false-cold-rebuild", benchmark+"-source-replay-v1/results.json",
                 ["cold_import_rebuild"], True, "replay/score binding differs: benchmark"),
                ("numerical-incomplete-sample-replay", benchmark+"-source-replay-v1/results.json",
                 ["identical_scalar_values"], 339, "replay/score binding differs: benchmark"),
                ("numerical-production-replay-bit-difference", production+"-source-replay-v1/results.json",
                 ["lean_float64_bit_differences"], 1, "replay differs: production"),
                ("numerical-false-certificate", production+"-v1/results.json",
                 ["new_certificates"], 1, "execution/proof scope differs: production"),
                ("numerical-unverified-download-tls", benchmark+"-publication-v1/results.json",
                 ["observations", 0, "tls_verification"], False, "anonymous publication differs: benchmark"),
                ("numerical-missing-download-observations", benchmark+"-publication-v1/results.json",
                 ["observations"], [], "anonymous publication differs: benchmark"),
                ("numerical-changed-source-pin", benchmark+"-source-replay-v1/results.json",
                 ["source_bindings_sha256"], "0"*64, "replay/score binding differs: benchmark"),
                ("numerical-missing-artifact-control", production+"-packet-controls-v1/results.json",
                 ["negative_controls"], 25, "counts differ: production"),
                ("numerical-original-result-overclaim", benchmark+"-v1/results.json",
                 ["original_paper_fully_reproduced"], True, "original-result overclaim: benchmark"),
            ]
            def numerical_control(item):
                control_name, selected, keys, value, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                record = json.loads(entries[selected])
                parent = record
                for key in keys[:-1]:
                    parent = parent[key]
                parent[keys[-1]] = value
                if control_name == "numerical-changed-sampled-value":
                    import struct
                    parent["float64_bits"] = str(struct.unpack(">Q", struct.pack(">d", value))[0])
                entries[selected] = (json.dumps(record, indent=2)+"\n").encode()
                manifest_name = str(Path(selected).with_name("manifest.json"))
                if manifest_name in entries:
                    manifest = json.loads(entries[manifest_name])
                    manifest.get("files", manifest)[Path(selected).name] = hashlib.sha256(entries[selected]).hexdigest()
                    entries[manifest_name] = (json.dumps(manifest, indent=2)+"\n").encode()
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "Numerical study " + expected_gate not in log:
                    raise RuntimeError("Numerical study control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                                "inner_receipt_hash_synchronized": True,
                                "gate": "frozen numerical report and receipt consistency"}
            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(numerical_control, cases))
            code, log = execute("positive-after-numerical-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-control standalone replay failed: " + log)
            results.append({"name": "positive-after-numerical-controls", "accepted": True,
                            "git_on_path": False})
        if "full_shape_models" in read(snapshot / "targets.json"):
            def model_control(item):
                control_name, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                config = read(altered / "targets.json")
                mutate_model_evidence(entries, config, control_name)
                write(altered / "targets.json", config)
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "Full-shape model " + expected_gate not in log:
                    raise RuntimeError("Full-shape model control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                        "inner_report_and_configuration_pins_synchronized": True,
                        "gate": "frozen model summary, metric and recorded replay consistency"}
            # Each worker mutates and executes only its own copied snapshot/log.
            # Per-replay limits remain 120 seconds; the public aggregate remains 300.
            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(model_control, MODEL_CONTROLS))
            code, log = execute("positive-after-model-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-model-control standalone replay failed: " + log)
            results.append({"name": "positive-after-model-controls", "accepted": True,
                            "git_on_path": False})
        if "ptx_pointwise_proof" in read(snapshot / "targets.json"):
            def ptx_control(item):
                control_name, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                config = read(altered / "targets.json")
                mutate_ptx_evidence(entries, config, control_name)
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "PTX pointwise " + expected_gate not in log:
                    raise RuntimeError("PTX pointwise control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                        "inner_packet_inventory_synchronized": True,
                        "gate": "frozen exact-source PTX proof/replay scope and actual source CI"}
            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(ptx_control, PTX_CONTROLS))
            code, log = execute("positive-after-ptx-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-PTX-control standalone replay failed: " + log)
            results.append({"name": "positive-after-ptx-controls", "accepted": True,
                            "git_on_path": False})
        if "ptx_dot_proof" in read(snapshot / "targets.json"):
            def gemv_control(item):
                control_name, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                config = read(altered / "targets.json")
                mutate_gemv_evidence(entries, config, control_name)
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "PTX dot " + expected_gate not in log:
                    raise RuntimeError("PTX GEMV control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                        "inner_packet_inventory_synchronized": True,
                        "gate": "frozen complete-source GEMV proof/replay scope and actual source CI"}
            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(gemv_control, GEMV_CONTROLS))
            code, log = execute("positive-after-gemv-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-GEMV-control standalone replay failed: " + log)
            results.append({"name": "positive-after-gemv-controls", "accepted": True, "git_on_path": False})
        if "ptx_matrix_proof" in read(snapshot / "targets.json"):
            def gemm_control(item):
                control_name, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                config = read(altered / "targets.json")
                mutate_gemm_evidence(entries, config, control_name)
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "PTX matrix " + expected_gate not in log:
                    raise RuntimeError("PTX GEMM control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                        "inner_packet_inventory_synchronized": True,
                        "gate": "frozen complete-source GEMM proof/replay scope and actual source CI"}
            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(gemm_control, GEMM_CONTROLS))
            code, log = execute("positive-after-gemm-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-GEMM-control standalone replay failed: " + log)
            results.append({"name": "positive-after-gemm-controls", "accepted": True, "git_on_path": False})
        for kind, key, controls, mutate in (
            ("bmm", "ptx_batched_proof", BMM_CONTROLS, mutate_bmm_evidence),
            ("linear", "ptx_linear_proof", LINEAR_CONTROLS, mutate_linear_evidence),
        ):
            if key not in read(snapshot / "targets.json"):
                continue

            def extended_control(item):
                control_name, expected_gate = item
                altered = root / control_name
                shutil.copytree(snapshot, altered)
                entries = packed_controls.entries.copy()
                config = read(altered / "targets.json")
                mutate(entries, config, control_name)
                packed_controls.write(altered, entries)
                rehash(altered, archive_changed=True)
                code, log = execute(control_name, altered)
                if code == 0 or "PTX " + kind + " " + expected_gate not in log:
                    raise RuntimeError("PTX " + kind + " control failed: " + control_name + "\n" + log)
                return {"name": control_name, "accepted": False, "fully_rehashed": True,
                        "inner_packet_inventory_synchronized": True,
                        "gate": "frozen complete-source proof/replay/failure scope and actual source CI"}

            with ThreadPoolExecutor(max_workers=2) as pool:
                results.extend(pool.map(extended_control, controls))
            code, log = execute("positive-after-" + kind + "-controls", isolated)
            if code or "frozen-snapshot-replayed" not in log:
                raise RuntimeError("Post-" + kind + "-control standalone replay failed: " + log)
            results.append({"name": "positive-after-" + kind + "-controls", "accepted": True,
                            "git_on_path": False})
        altered = root / "traversal"
        shutil.copytree(snapshot, altered)
        entries = packed_controls.entries.copy()
        unsafe = "../lark-paper-control-" + uuid.uuid4().hex
        entries[unsafe] = b"must not be extracted"
        packed_controls.write(altered, entries)
        rehash(altered, archive_changed=True)
        code, log = execute("fully-rehashed-traversal", altered)
        traversal_gate = ("Unsafe evidence path" if read(snapshot / "provenance.json")["schema"] == 2
                          else "Unsafe path: " + unsafe)
        if code == 0 or traversal_gate not in log:
            raise RuntimeError("Wrong traversal-control outcome: " + log)
        results.append(
            {
                "name": "fully-rehashed-traversal",
                "accepted": False,
                "fully_rehashed": True,
                "gate": "safe archive path",
            }
        )
        wrong = root / "wrong-manuscript.tar"
        wrong.write_bytes(b"wrong manuscript bytes")
        code, log = execute("wrong-manuscript", isolated, wrong)
        if code == 0 or "Unexpected manuscript archive" not in log:
            raise RuntimeError("Wrong manuscript-control outcome: " + log)
        results.append(
            {"name": "wrong-manuscript", "accepted": False, "gate": "pinned manuscript digest"}
        )
    write(
        out / "results.json",
        {
            "status": "passed",
            "checks": results,
            "positive_replays": sum(row["accepted"] for row in results),
            "negative_controls": sum(not row["accepted"] for row in results),
            "source_snapshot_manifest_sha256": sha(snapshot / "manifest.json"),
            "replayer_sha256": sha(Path(__file__).with_name("replay_snapshot.py")),
            "control_runner_sha256": sha(Path(__file__)),
            "fresh_lean_checks": 0,
            "fresh_gpu_trials": 0,
            "model_calls": 0,
            "original_paper_fully_reproduced": False,
        },
    )
    write(out / "manifest.json", {n: sha(out / n) for n in sorted(file_set(out))})
    print(
        json.dumps(
            {
                "status": "passed",
                "outside_checkout_without_git": True,
                "positive_replays": sum(row["accepted"] for row in results),
                "negative_controls": sum(not row["accepted"] for row in results),
                "fresh_lean_checks": 0,
                "fresh_gpu_trials": 0,
                "model_calls": 0,
            }
        )
    )


if __name__ == "__main__":
    main()
