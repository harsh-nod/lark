"""Check frozen PTX ReLU evidence without executing captured code or proofs.

This checks the recorded source, proof, replay, control and publication bindings.
It repeats no Lean/model/GPU experiment and establishes no hardware conformance.
"""

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


ROOT = Path(__file__).resolve().parents[2]
PREFIX = "reproduction/ptx/results/full-size-relu-proof-v1"
PUBLICATION = "reproduction/ptx/results/full-size-relu-proof-publication-v1"
CI = "reproduction/ptx/results/full-size-relu-proof-ci-v1"
PRODUCER = "502f94c0bf845615aad06abdd099e7052f2e82cf"
PUBLISHED = "bc96d41eaa397e9d51aa15c0b36124039fc2241f"
LEAN = "92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023"
MAIN = "38a8c57bc1904f6f9eed224f109783b82323b36033646e8c576022f55b95b92c"
SOURCE_BINDINGS = "8118fd02e3cdcdbca461117f9e42a05d7652357cfc96c5f534103355340b5e52"
INPUTS = {
    "kernel.ptx": "7796e78074f76e2955dee35860c6ca3cb0dcc3263e9115480c9d57b66b676848",
    "reference.py": "b13620a151f3ca39b16eea83ea8330e140385b5344e3dc940f17417026c69241",
    "contract.json": "63815c7d03596dc7ae001fb39ce3bf27f6bd05573655f0b4505782685778d979",
}
LIMITS = {"maxRecDepth": 10000, "maxHeartbeats": 2000000,
          "per_Lean_process_seconds": 180, "source_import_build_seconds": 600}
SCOPE = ("Direct source-bound finite PTX FP16 pointwise proof against the closed reference AST. "
         "Every parsed instruction executes in the declared abstract model; all grid blocks, actual "
         "memory-event race freedom and every reference output are covered. The original scalar CUDA "
         "contract, shapes, dtypes, geometry and CUDA fuel remain unchanged. PTX execution is "
         "structurally finite and consumes every instruction; the CUDA fuel is data for its separate "
         "model, not a bound of four PTX instructions. Python parsing/reference formalization, pointer "
         "provenance, aligned disjoint non-wrapping allocations and scalar-operation correspondence "
         "remain trusted. No IEEE/error-bound, NVIDIA execution/conformance, original optimized kernel "
         "or original model-result claim. This separate development checker registers no new legacy "
         "SDK profile or model success.")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TAGS = {"LarkPtxCertificate." + name for name in (
    "source_program", "reference_body", "launch", "race_free", "segment_equivalence", "kernel_eq_spec")}
JOBS = {"reference-identity", "native-awq-real", "native-awq-components", "native-sglang-real",
        "native-flashinfer-real", "native-sglang-rmsnorm", "native-flashinfer-rmsnorm",
        "native-qknorm-rope", "native-rope", "softmax-source", "softmax-block", "softmax-grid",
        "softmax-race", "softmax-real", "exact-real", "qknorm-rope-split-real", "qknorm-rope-real",
        "fused-real", "proof-tests"}


def require(ok, message):
    if not ok:
        raise ValueError("PTX pointwise " + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def counters(record, expected, message):
    require(all(type(record.get(k)) is int and record[k] == v for k, v in expected.items()), message)


def audits(data):
    matches = re.findall(r"'([^']+)'\s+(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
                         data.decode())
    result = {name: sorted(value.strip() for value in values.split(",") if value.strip())
              for name, _, values in matches}
    require(len(result) == len(matches) and all(set(value) <= ALLOWED for value in result.values()),
            "positive axiom audit differs")
    return result


def check_recording_packet(root, *, declared=None):
    """Inspect the actual five archives as data, with no SDK/Lean dependency."""
    root = Path(root).resolve()

    def content(name):
        relative = PurePosixPath(name)
        require(not relative.is_absolute() and ".." not in relative.parts and str(relative) == name,
                "unsafe recording path")
        local = root / name
        require(local.is_file() and not local.is_symlink() and local.resolve().is_relative_to(root),
                "recording path differs")
        require(declared is None or name in declared, "undeclared recording file")
        return local.read_bytes()

    def read(name):
        return json.loads(content(name))

    manifest = read("manifest.json")
    require({p.name for p in root.iterdir() if p.is_file()} == set(manifest) | {"manifest.json"}
            and all(sha(content(name)) == digest for name, digest in manifest.items()),
            "packet inventory differs")
    report = read("results.json")
    require(report["status"] == "exact-source-full-size-PTX-ReLU-proof-evidence"
            and report["producer_commit"] == PRODUCER
            and report["profile"] == "ptx-fp16-pointwise-finite-v1", "recording identity differs")
    counters(report, {"independent_source_bound_development_proofs": 1,
                     "retained_positive_Main_checks": 4, "positive_rechecks": 3,
                     "owned_module_builds_across_four_checks": 12, "elements": 16384,
                     "PTX_instructions": 15, "direct_Lean_negative_controls": 4, "negative_timeouts": 0,
                     "new_registered_source_certificates": 0, "packaging_model_calls": 0,
                     "packaging_Lean_checks": 0, "packaging_gpu_trials": 0,
                     "model_calls_for_this_proof_study": 0, "gpu_trials_for_this_proof_study": 0},
             "kernel/recheck/execution counters differ")
    require(report["nvidia_execution"] is report["original_paper_fully_reproduced"] is False
            and report["limits"] == LIMITS and report["dtype"] == "float16" and report["scope"] == SCOPE
            and report["launch"] == {"grid": 16384, "block": 1, "warp": 32}
            and report["unchanged_CUDA_contract_fuel"] == [4, 1, 1, 1]
            and report["main_sha256"] == MAIN and report["input_bindings"] == INPUTS
            and report["lean_binary_sha256"] == LEAN, "proof contract/original scope differs")
    require(set(report["archives"]) == {"export", "replay", "controls", "installed-wheel", "wheel-build"},
            "archive roster differs")
    archives = {}
    for label, binding in report["archives"].items():
        data, inventory = content(label + ".tar.gz"), read(label + "-files.json")
        require(sha(data) == binding["archive_sha256"]
                and sha(content(label + "-files.json")) == binding["inventory_sha256"],
                "archive binding differs")
        entries = {}
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            members = archive.getmembers()
            require(len(members) == len(inventory) == binding["files"]
                    and sum(member.size for member in members) == binding["uncompressed_bytes"]
                    and sum(member.size for member in members) <= 40_000_000,
                    "archive size/inventory differs")
            for member in members:
                name = PurePosixPath(member.name)
                require(member.isfile() and not name.is_absolute() and ".." not in name.parts
                        and str(name) == member.name and member.name not in entries
                        and member.name in inventory, "unsafe archive member")
                entries[member.name] = archive.extractfile(member).read()
                require(sha(entries[member.name]) == inventory[member.name], "archive member hash differs")
        require(set(entries) == set(inventory), "archive inventory differs")
        archives[label] = entries

    export_manifest = sha(archives["export"]["manifest.json"])
    positives = [archives["export"], archives["replay"],
                 {n.removeprefix("positive-source-only-replay/"): data
                  for n, data in archives["controls"].items() if n.startswith("positive-source-only-replay/")},
                 {n.removeprefix("source-only-replay/"): data
                  for n, data in archives["installed-wheel"].items() if n.startswith("source-only-replay/")}]
    for i, entries in enumerate(positives):
        inner = json.loads(entries["manifest.json"])
        require({n: sha(data) for n, data in entries.items() if n != "manifest.json"} == inner,
                "positive inner inventory differs")
        proof = json.loads(entries["results.json"])
        require(proof["status"] == "verified-source-bound-finite-PTX"
                and proof["source_bound_proof_accepted"] is True
                and proof["scope"] == report["scope"] and proof["limits"] == LIMITS
                and proof["source_language"] == "ptx" and proof["reference_contract_language"] == "cuda"
                and proof["input_bindings"] == INPUTS
                and all(sha(entries[n]) == digest for n, digest in INPUTS.items())
                and proof["main_sha256"] == sha(entries["Main.lean"]) == MAIN
                and proof["lean_binary_sha256"] == LEAN
                and proof["old_owned_olean_cache_used"] is False,
                "positive source/contract/proof binding differs")
        counters(proof, {"elements": 16384, "PTX_instructions": 15,
                         "owned_Lean_modules_freshly_compiled": 3, "model_calls": 0, "gpu_trials": 0,
                         "new_registered_source_certificates": 0}, "positive proof counters differ")
        require(proof["nvidia_execution"] is proof["original_paper_fully_reproduced"] is False
                and proof["launch"] == report["launch"]
                and proof["unchanged_CUDA_contract_fuel"] == [4, 1, 1, 1],
                "positive execution/contract scope differs")
        checks = [*proof["module_checks"], proof["main_check"]]
        require(len(checks) == 4 and all(type(c["exit_code"]) is int and c["exit_code"] == 0
                and c["timed_out"] is False and c["timeout_seconds"] == 180 for c in checks),
                "positive checker completion differs")
        require(proof["axiom_audits"] == audits(entries["Main.log"])
                and set(proof["axiom_audits"]) == TAGS
                and proof["library_axiom_audits"] == audits(entries["PtxPointwise.log"])
                and len(proof["library_axiom_audits"]) == 22,
                "positive axiom audit differs")
        source_bindings = json.loads(entries["source-bindings.json"])
        require(proof["source_bindings_sha256"] == sha(entries["source-bindings.json"]) == SOURCE_BINDINGS
                and len(source_bindings) == 12 and all(sha(entries["owned-sources/" + n]) == digest
                for n, digest in source_bindings.items())
                and source_bindings == json.loads(positives[0]["source-bindings.json"]),
                "trusted source identity differs")
        for check, name in zip(checks, ("Nonlinear.log", "Pointwise.log", "PtxPointwise.log", "Main.log"),
                               strict=True):
            require(check["log_sha256"] == sha(entries[name]), "positive log binding differs")
        if i:
            replay = json.loads(entries["replay.json"])
            require(replay["status"] == "fresh-source-only-PTX-proof-replay-passed"
                    and replay["main_regenerated_identically"] is True
                    and replay["recording_manifest_sha256"] == export_manifest
                    and replay["fresh_export_manifest_sha256"] == sha(entries["proof-export-manifest.json"])
                    and replay["main_sha256"] == MAIN and replay["old_owned_olean_cache_used"] is False,
                    "fresh source-only replay binding differs")
            counters(replay, {"owned_modules_freshly_compiled": 3, "model_calls": 0, "gpu_trials": 0,
                              "new_registered_source_certificates": 0}, "replay counters differ")
            require(replay["fresh_export_axiom_audits"] == proof["axiom_audits"]
                    and replay["nvidia_execution"] is replay["original_paper_fully_reproduced"] is False,
                    "replay execution scope differs")

    controls = json.loads(archives["controls"]["results.json"])
    require(controls == read("controls-results.json")
            and controls["status"] == "full-size-PTX-ReLU-source-controls-passed"
            and controls["recording_manifest_sha256"] == export_manifest
            and controls["direct_Lean_negative_controls"] == 4
            and controls["timeouts"] == 0
            and {c["control"] for c in controls["negative_controls"]}
            == {"wrong-arithmetic", "misaligned-byte-stride", "wrong-output-address", "skipped-half-conversion"},
            "source-control roster differs")
    counters(controls, {"positive_controls": 1, "source_bound_proofs_added": 0,
                        "new_registered_source_certificates": 0, "model_calls": 0, "gpu_trials": 0},
             "control execution counters differ")
    require(controls["nvidia_execution"] is controls["original_paper_fully_reproduced"] is False
            and controls["positive"] == json.loads(positives[2]["replay.json"]),
            "control execution scope differs")
    for control in controls["negative_controls"]:
        base = control["control"] + "/"
        require(control["reader_accepted"] is True and control["Lean"]["timed_out"] is False
                and type(control["Lean"]["exit_code"]) is int and control["Lean"]["exit_code"] != 0
                and control["channel"] == "source-program-equality-proof-refused"
                and control["general_kernel_falsity_claim"] is False
                and control["all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged"] is True
                and control["source_sha256"] == sha(archives["controls"][base + "kernel.ptx"])
                and control["main_sha256"] == sha(archives["controls"][base + "Main.lean"])
                and control["Lean"]["log_sha256"] == sha(archives["controls"][base + "Main.log"]),
                "direct Lean binding-control scope differs")
    installed = json.loads(archives["installed-wheel"]["results.json"])
    wheel = archives["wheel-build"]["lark_kernels-0.1.0-py3-none-any.whl"]
    require(installed == read("installed-wheel-results.json")
            and installed["status"] == "installed-wheel-source-only-replay-passed"
            and installed["exit_code"] == 0 and installed["checkout_imported"] is False
            and installed["isolated_mode"] is True and installed["network_during_install_and_replay"] is False
            and installed["wheel_sha256"] == sha(wheel) == report["wheel_sha256"],
            "installed-wheel replay differs")
    require(installed["nvidia_execution"] is installed["original_paper_fully_reproduced"] is False,
            "installed-wheel execution scope differs")
    counters(installed, {"new_registered_source_certificates": 0, "model_calls": 0, "gpu_trials": 0},
             "installed-wheel execution counters differ")
    require(read("proof-results.json") == json.loads(positives[0]["results.json"])
            and read("replay-results.json") == json.loads(positives[1]["replay.json"]),
            "copied proof/replay summary differs")
    return {"independent_source_bound_development_proofs": 1, "retained_positive_Main_checks": 4,
            "positive_rechecks": 3, "direct_Lean_negative_controls": 4, "elements": 16384,
            "PTX_instructions": 15, "new_registered_source_certificates": 0,
            "fresh_experiments_by_ledger": False, "nvidia_execution": False,
            "original_paper_fully_reproduced": False, "source_commit": PUBLISHED,
            "scope": "Recorded exact-source finite abstract PTX ReLU proof and replay/control bindings. "
                     "One kernel, not four independent proofs or a model success. No IEEE/error-bound, "
                     "NVIDIA execution/conformance or original optimized-kernel/table result."}


def check_ptx_pointwise_evidence(config, root=ROOT):
    root = Path(root).resolve()
    spec = config["ptx_pointwise_proof"]
    require(spec == {"prefix": PREFIX, "publication_prefix": PUBLICATION, "ci_prefix": CI},
            "declared evidence roster differs")
    declared = {p for group in config["evidence_groups"].values() for p in group}
    report = check_recording_packet(root / PREFIX,
                                   declared={p[len(PREFIX) + 1:] for p in declared if p.startswith(PREFIX + "/")})

    def content(prefix, name):
        relative = PurePosixPath(name)
        require(not relative.is_absolute() and ".." not in relative.parts and str(relative) == name,
                "unsafe auxiliary evidence path")
        path = prefix + "/" + name
        local = root / path
        require(path in declared and local.is_file() and not local.is_symlink()
                and local.resolve().is_relative_to(root), "auxiliary evidence path differs")
        return local.read_bytes()

    def read(prefix, name):
        return json.loads(content(prefix, name))

    for prefix in (PUBLICATION, CI):
        manifest = read(prefix, "manifest.json")
        require(set(p[len(prefix) + 1:] for p in declared if p.startswith(prefix + "/"))
                == set(manifest) | {"manifest.json"}
                and all(sha(content(prefix, n)) == digest
                        for n, digest in manifest.items()), "auxiliary inventory differs")
    publication = read(PUBLICATION, "results.json")
    source_files = {"README.md", "reproduction/ptx/README.md", "reproduction/ptx/POINTWISE.md",
                    "lark_kernels/ptx_pointwise.py", "lark_kernels/ptx_pointwise_certificate.py",
                    "lean/Lark/PtxPointwise.lean", "pyproject.toml",
                    "reproduction/ptx/check_pointwise_controls.py", "tests/test_ptx_pointwise.py"}
    packet_files = {PREFIX + "/" + p.name for p in (root / PREFIX).iterdir() if p.is_file()}
    require(publication["status"] == "anonymous-exact-source-full-size-PTX-ReLU-proof-publication-verified"
            and publication["source_commit"] == PUBLISHED
            and publication["all_downloads_match_committed_bytes"] is True
            and publication["tls_verification"] is True and publication["authorization_header"] is False
            and len(publication["downloaded_files"]) == 28
            and {row["path"] for row in publication["downloaded_files"]} == source_files | packet_files
            and publication["total_downloaded_bytes"]
            == sum(row["bytes"] for row in publication["downloaded_files"])
            and all(row["matches_committed_bytes"] is row["tls_verification"] is True
                    and row["authorization_header"] is False and row["http_status"] == 200
                    and row["curl_ssl_verify_result"] == 0
                    and (row["path"] not in packet_files
                         or row["sha256"] == sha((root / row["path"]).read_bytes()))
                    for row in publication["downloaded_files"]),
            "anonymous publication scope differs")
    counters(publication, {"model_calls": 0, "gpu_trials": 0, "fresh_lean_checks": 0,
                           "new_registered_certificates": 0}, "publication execution counters differ")
    require(publication["original_paper_fully_reproduced"] is False, "publication original scope differs")
    summary, run, response = (read(CI, name) for name in ("results.json", "run.json", "jobs.json"))
    jobs = response["jobs"]
    require(summary["status"] == "exact-source-CI-all-19-passed" and summary["source_commit"] == PUBLISHED
            and summary["run_id"] == run["id"] == 43444864484
            and summary["successful_jobs"] == 19 and set(summary["expected_jobs"]) == JOBS
            and run["head_sha"] == PUBLISHED and run["event"] == "push" and run["name"] == "Verify"
            and run["head_branch"] == "reproduction/ptx-pointwise-refinement"
            and run["status"] == "completed" and run["conclusion"] == "success"
            and response["total_count"] == len(jobs) == len({j["id"] for j in jobs}) == 19
            and {j["name"] for j in jobs} == JOBS
            and all(j["status"] == "completed" and j["conclusion"] == "success" for j in jobs)
            and summary["original_paper_fully_reproduced"] is False, "actual source CI differs")
    counters(summary, {"model_calls": 0, "gpu_trials": 0, "CI_reruns": 0,
                       "new_registered_source_certificates": 0}, "source CI execution counters differ")
    report.update(anonymous_publication_files=28, successful_source_CI_jobs=19)
    return report
