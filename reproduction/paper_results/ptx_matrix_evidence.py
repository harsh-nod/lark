"""Check frozen PTX GEMM evidence without executing captured code or proofs.

This checks the recorded source, proof, replay, control and publication bindings.
It repeats no Lean/model/GPU experiment and establishes no hardware conformance.
"""

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[2]
PREFIX = "reproduction/ptx/results/full-size-gemm-proof-v1"
PUBLICATION = "reproduction/ptx/results/full-size-gemm-proof-publication-v2"
CI = "reproduction/ptx/results/full-size-gemm-proof-ci-v2"
PRODUCER = "c1f6e9220c36df38152dd738fa812288bec64eb7"
PUBLISHED = "a2100f361d451fafd9babb853319a3fcd6bf5c82"
LEAN = "92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023"
MAIN = "9d074157e0e7a818e8b90b0e2dea8062ec370dbd287371f9a3236f57cbb7f3f4"
SOURCE_BINDINGS = "c9f22b9a308ebe6854c50d4e881357ac234fe8727b3ffd70b6822a1afeef0288"
INPUTS = {
    "kernel.ptx": "896f2337328f9bb0b62975117174405f0eab90560fe91c672beb31094e86c74c",
    "reference.py": "18cc07d00af098bcc9c2d94fb5b3805f4264c810d64ca9814c07e9e25f0db466",
    "contract.json": "2a2eb23fa4daf7b7a97bb7024e2e53648952698b0f6747e5609e89f3b4309f41",
}
LIMITS = {"maxRecDepth": 10000, "maxHeartbeats": 2000000,
          "per_Lean_process_seconds": 180, "source_import_build_seconds": 600}
SCOPE = 'Source-bound complete compiled 64x256 times 256x512 FP16 GEMM development proof. All 171 actual parsed instructions, the 47-instruction prologue, all 16 iterations of the real sixteen-term backward loop, the five control instructions, epilogue and ret, all 32768 active lanes, actual access-trace race freedom, every extracted reference output and preservation outside the output footprint are covered under the declared abstract scalar interpretation. The unchanged CUDA shape/dtypes, grid 32768/block 1/warp 32 and fuel [1030,1,1,1] are retained. Finite PTX execution is an inductive sequence of actual successful transitions; CUDA fuel remains separate data, with no new execution fuel. Python parsing/reference formalization, logical pointer provenance, aligned disjoint non-wrapping allocations and scalar-operation correspondence remain trusted. No IEEE/error-bound, PyTorch/NVIDIA hardware-conformance, original optimized kernel, original model-result or original-paper-completion claim. This separate development checker registers no legacy SDK profile or model success.'

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TAGS = {"LarkPtxMatrixCertificate." + name for name in (
    "source_program", "reference_body", "launch", "race_free", "segment_equivalence", "kernel_eq_spec")}
JOBS = {"reference-identity", "native-awq-real", "native-awq-components", "native-sglang-real",
        "native-flashinfer-real", "native-sglang-rmsnorm", "native-flashinfer-rmsnorm",
        "native-qknorm-rope", "native-rope", "softmax-source", "softmax-block", "softmax-grid",
        "softmax-race", "softmax-real", "exact-real", "qknorm-rope-split-real", "qknorm-rope-real",
        "fused-real", "proof-tests", "paper-ledger", "ptx-matrix"}


def require(ok, message):
    if not ok:
        raise ValueError("PTX matrix " + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def same_json(actual, expected):
    options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
    return json.dumps(actual, **options) == json.dumps(expected, **options)


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
    require(report["status"] == "exact-source-full-size-PTX-GEMM-proof-evidence"
            and report["producer_commit"] == PRODUCER
            and report["profile"] == "source-bound-compiled-gemm-fp16-v1", "recording identity differs")
    counters(report, {"independent_source_bound_development_proofs": 1,
                     "retained_positive_Main_checks": 4, "positive_rechecks": 3,
                     "owned_module_builds_across_four_checks": 20,
                     "PTX_instructions": 171, "direct_Lean_negative_controls": 4, "negative_timeouts": 0,
                     "new_registered_source_certificates": 0, "packaging_model_calls": 0,
                     "packaging_Lean_checks": 0, "packaging_gpu_trials": 0,
                     "model_calls_for_this_proof_study": 0, "gpu_trials_for_this_proof_study": 0},
             "kernel/recheck/execution counters differ")
    require(same_json(report["shapes"], [[64,256],[256,512],[64,512]]), "proof contract/original scope differs")
    require(report["nvidia_execution"] is report["original_paper_fully_reproduced"] is False
            and same_json(report["limits"], LIMITS) and report["dtype"] == "float16" and report["scope"] == SCOPE
            and same_json(report["launch"], {"grid": 32768, "block": 1, "warp": 32})
            and same_json(report["unchanged_CUDA_contract_fuel"], [1030, 1, 1, 1])
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
        require(proof["status"] == "verified-source-bound-full-PTX-GEMM"
                and proof["source_bound_proof_accepted"] is True
                and proof["scope"] == report["scope"] and same_json(proof["limits"], LIMITS)
                and same_json(proof["shapes"], [[64,256],[256,512],[64,512]])
                and proof["dtypes"] == ["float16", "float16", "float16"]
                and proof["source_language"] == "ptx" and proof["reference_contract_language"] == "cuda"
                and proof["input_bindings"] == INPUTS
                and all(sha(entries[n]) == digest for n, digest in INPUTS.items())
                and proof["main_sha256"] == sha(entries["Main.lean"]) == MAIN
                and proof["lean_binary_sha256"] == LEAN
                and proof["old_owned_olean_cache_used"] is False,
                "positive source/contract/proof binding differs")
        counters(proof, {"PTX_instructions": 171, "source_bound_development_proofs": 1,
                         "owned_Lean_modules_freshly_compiled": 5, "model_calls": 0, "gpu_trials": 0,
                         "new_registered_source_certificates": 0}, "positive proof counters differ")
        require(proof["nvidia_execution"] is proof["original_paper_fully_reproduced"] is False
                and same_json(proof["launch"], report["launch"])
                and same_json(proof["unchanged_CUDA_contract_fuel"], [1030, 1, 1, 1]),
                "positive execution/contract scope differs")
        require(same_json(json.loads(entries["reference-ast.json"]),
                ["toHalf", ["matmul", ["fromHalf", ["input",0]], ["fromHalf", ["input",1]]]])
                and proof["reference_ast_sha256"] == sha(entries["reference-ast.json"]),
                "positive reference AST differs")
        require([row["module"] for row in proof["module_checks"]] ==
                ["Lark.Nonlinear", "Lark.Pointwise", "Lark.PtxPointwise", "Lark.PtxDot", "Lark.PtxMatrix"],
                "positive module roster differs")
        checks = [*proof["module_checks"], proof["main_check"]]
        require(len(checks) == 6 and all(type(c["exit_code"]) is int and c["exit_code"] == 0
                and c["timed_out"] is False and c["timeout_seconds"] == 180 for c in checks),
                "positive checker completion differs")
        require(proof["axiom_audits"] == audits(entries["Main.log"])
                and set(proof["axiom_audits"]) == TAGS
                and proof["library_axiom_audits"] == {name: value for module in ("Nonlinear", "Pointwise", "PtxPointwise", "PtxDot", "PtxMatrix")
                    for name, value in audits(entries[module+".log"]).items()}
                and len(proof["library_axiom_audits"]) == 169,
                "positive axiom audit differs")
        source_bindings = json.loads(entries["source-bindings.json"])
        require(proof["source_bindings_sha256"] == sha(entries["source-bindings.json"]) == SOURCE_BINDINGS
                and len(source_bindings) == 55 and all(sha(entries["owned-sources/" + n]) == digest
                for n, digest in source_bindings.items())
                and source_bindings == json.loads(positives[0]["source-bindings.json"]),
                "trusted source identity differs")
        for check, name in zip(checks, ("Nonlinear.log", "Pointwise.log", "PtxPointwise.log", "PtxDot.log", "PtxMatrix.log", "Main.log"),
                               strict=True):
            require(check["log_sha256"] == sha(entries[name]), "positive log binding differs")
        if i:
            replay = json.loads(entries["replay.json"])
            require(replay["status"] == "fresh-source-only-PTX-GEMM-proof-replay-passed"
                    and replay["main_regenerated_identically"] is True
                    and replay["recording_manifest_sha256"] == export_manifest
                    and replay["fresh_export_manifest_sha256"] == sha(entries["proof-export-manifest.json"])
                    and replay["main_sha256"] == MAIN and replay["old_owned_olean_cache_used"] is False,
                    "fresh source-only replay binding differs")
            counters(replay, {"owned_modules_freshly_compiled": 5, "model_calls": 0, "gpu_trials": 0,
                              "positive_rechecks": 1, "source_bound_proofs_added": 0,
                              "new_registered_source_certificates": 0}, "replay counters differ")
            require(replay["fresh_export_axiom_audits"] == proof["axiom_audits"]
                    and replay["nvidia_execution"] is replay["original_paper_fully_reproduced"] is False,
                    "replay execution scope differs")

    controls = json.loads(archives["controls"]["results.json"])
    require(controls == read("controls-results.json")
            and controls["status"] == "full-size-PTX-GEMM-source-controls-passed"
            and controls["recording_manifest_sha256"] == export_manifest
            and len(controls["negative_controls"]) == 4
            and {c["control"] for c in controls["negative_controls"]}
            == {"wrong-product", "wrong-loop-counter-stride", "wrong-B-pointer-stride", "conflicting-output-address"},
            "source-control roster differs")
    counters(controls, {"positive_controls": 1, "source_bound_proofs_added": 0,
                        "direct_Lean_negative_controls": 4, "timeouts": 0,
                        "owned_modules_freshly_compiled": 5,
                        "new_registered_source_certificates": 0, "model_calls": 0, "gpu_trials": 0},
             "control execution counters differ")
    require(controls["nvidia_execution"] is controls["original_paper_fully_reproduced"] is False
            and controls["positive"] == json.loads(positives[2]["replay.json"]),
            "control execution scope differs")
    for control in controls["negative_controls"]:
        base = control["control"] + "/"
        log = archives["controls"][base + "Main.log"].decode()
        main = archives["controls"][base + "Main.lean"].decode()
        line = next(i + 1 for i, text in enumerate(main.splitlines())
                    if text.startswith("theorem source_program "))
        errors = {int(value) for value in re.findall(r"Main\.lean:([0-9]+):[0-9]+: error:", log)}
        require(control["reader_accepted"] is True and control["Lean"]["timed_out"] is False
                and type(control["Lean"]["exit_code"]) is int and control["Lean"]["exit_code"] != 0
                and control["channel"] == "source-program-equality-proof-refused"
                and control["general_kernel_falsity_claim"] is False
                and control["all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged"] is True
                and control["source_sha256"] == sha(archives["controls"][base + "kernel.ptx"])
                and control["main_sha256"] == sha(archives["controls"][base + "Main.lean"])
                and control["Lean"]["log_sha256"] == sha(archives["controls"][base + "Main.log"])
                and json.loads(archives["controls"][base + "results.json"]) == control
                and sha(archives["controls"][base + "contract.json"]) == INPUTS["contract.json"]
                and sha(archives["controls"][base + "reference.py"]) == INPUTS["reference.py"],
                "direct Lean binding-control scope differs")
        counters(control, {"PTX_instructions": 171, "source_fragments_changed": 1},
                 "direct Lean binding-control scope differs")
        require(line in errors and "tactic 'decide' proved that" in log and "is false" in log
                and not any(marker in log for marker in (
                    "maximum recursion", "maximum number of heartbeats", "Stack overflow")),
                "direct Lean binding-control refusal differs")
    installed = json.loads(archives["installed-wheel"]["results.json"])
    wheel = archives["wheel-build"]["lark_kernels-0.2.0-py3-none-any.whl"]
    require(installed == read("installed-wheel-results.json")
            and installed["status"] == "installed-wheel-source-only-PTX-GEMM-replay-passed"
            and installed["exit_code"] == 0 and installed["checkout_imported"] is False
            and installed["isolated_mode"] is True and installed["network_during_install_and_replay"] is False
            and installed["git_on_PATH"] is False and installed["all_owned_source_bindings_match"] is True
            and installed["legacy_ReLU_owned_source_bindings_match"] is True
            and installed["legacy_ReLU_Main_regenerated_identically"] is True
            and all(installed[k] is True for k in ("legacy_GEMV_52_source_bindings_unchanged",
                "legacy_GEMV_Main_regenerated_identically", "legacy_GEMV_new_source_roster_refused_before_output",
                "legacy_GEMV_frozen_0_1_wheel_hash_unchanged"))
            and installed["wheel_sha256"] == sha(wheel) == report["wheel_sha256"],
            "installed-wheel replay differs")
    require(installed["nvidia_execution"] is installed["original_paper_fully_reproduced"] is False,
            "installed-wheel execution scope differs")
    counters(installed, {"new_registered_source_certificates": 0, "model_calls": 0, "gpu_trials": 0,
                         "owned_modules_freshly_compiled": 5, "source_bound_proofs_added": 0},
             "installed-wheel execution counters differ")
    build = json.loads(archives["wheel-build"]["build-results.json"])
    require(build == read("wheel-build-results.json")
            and build["status"] == "wheel-built-and-owned-GEMM-sources-byte-checked"
            and build["backend"] == {"setuptools": "80.9.0", "wheel": "0.45.1"}
            and build["wheel_sha256"] == sha(wheel)
            and build["all_five_owned_Lean_files_included"] is True
            and build["network_during_build"] is False, "wheel build scope differs")
    counters(build, {"exit_code": 0, "wheel_bytes": len(wheel), "model_calls": 0, "gpu_trials": 0,
                     "new_registered_source_certificates": 0, "owned_source_bindings_checked": 55}, "wheel build counters differ")
    with zipfile.ZipFile(io.BytesIO(wheel)) as zipped:
        bindings = json.loads(positives[0]["source-bindings.json"])
        for name, digest in bindings.items():
            if name.startswith("python/"):
                member = "lark_kernels/" + name[7:]
            else:
                members = [n for n in zipped.namelist() if n.endswith("/share/lark/" + name)]
                require(len(members) == 1, "wheel owned Lean source roster differs")
                member = members[0]
            require(sha(zipped.read(member)) == digest, "wheel trusted source identity differs")
    require(read("proof-results.json") == json.loads(positives[0]["results.json"])
            and read("replay-results.json") == json.loads(positives[1]["replay.json"]),
            "copied proof/replay summary differs")
    return {"independent_source_bound_development_proofs": 1, "retained_positive_Main_checks": 4,
            "positive_rechecks": 3, "direct_Lean_negative_controls": 4,
            "shapes": [[64,256],[256,512],[64,512]], "owned_module_builds_across_four_checks": 20,
            "PTX_instructions": 171, "new_registered_source_certificates": 0,
            "fresh_experiments_by_ledger": False, "nvidia_execution": False,
            "original_paper_fully_reproduced": False, "source_commit": PUBLISHED,
            "scope": "Recorded exact-source complete abstract PTX GEMM proof and replay/control bindings. "
                     "One kernel, not four independent proofs or a model success. No IEEE/error-bound, "
                     "NVIDIA execution/conformance or original optimized-kernel/table result."}


def check_ptx_matrix_evidence(config, root=ROOT):
    root = Path(root).resolve()
    spec = config["ptx_matrix_proof"]
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
    source_files = {".github/workflows/ci.yml", "README.md", "pyproject.toml",
                    "lark_kernels/ptx_matrix.py", "lark_kernels/ptx_matrix_certificate.py",
                    "lean/Lark/PtxMatrix.lean", "reproduction/ptx/MATRIX.md", "reproduction/ptx/README.md",
                    "reproduction/ptx/matrix_frontend.py", "reproduction/ptx/check_matrix_controls.py",
                    "tests/test_ptx_matrix.py", "tests/test_ptx_matrix_frontend.py"}
    source_files.update("reproduction/ptx/full-size/gemm/" + name for name in
                        ("README.md", "kernel.ptx", "reference.py", "source-bindings.json", "task.json"))
    source_files.update("reproduction/paper_results/snapshot-v24-ci-main-v1/" + name for name in
                        ("manifest.json", "promotion-driver.py", "promotion.json", "results.json", "source-ci.json"))
    source_files.update("reproduction/ptx/results/full-size-gemm-proof-publication-v1/" + name for name in
                        ("manifest.json", "binding.json", "results.json", "verifier.py"))
    source_files.update("reproduction/ptx/results/full-size-gemm-proof-ci-failed-v1/" + name for name in
                        ("manifest.json", "observer.py", "progress.json", "results.json", "run.json", "jobs.json"))
    source_files.update("reproduction/ptx/results/full-size-gemm-proof-ci-failure-log-v1/" + name for name in
                        ("manifest.json", "failed.log", "failure-analysis.json", "observation.json", "stderr.log"))
    packet_files = {PREFIX + "/" + p.name for p in (root / PREFIX).iterdir() if p.is_file()}
    require(publication["status"] == "anonymous-exact-source-full-size-PTX-GEMM-proof-publication-verified"
            and publication["source_commit"] == PUBLISHED
            and publication["all_downloads_match_committed_bytes"] is True
            and publication["tls_verification"] is True and publication["authorization_header"] is False
            and len(publication["downloaded_files"]) == 59
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
                           "new_registered_certificates": 0, "total_downloaded_bytes": 22753879,
                           "archives_checked": 5, "archive_members_checked": 382,
                           "owned_source_bindings_checked": 55, "prior_failed_source_CI_runs_retained": 1}, "publication execution counters differ")
    require(publication["original_paper_fully_reproduced"] is False, "publication original scope differs")
    binding = read(PUBLICATION, "binding.json")
    require(binding["source_commit"] == PUBLISHED and binding["TLS_verified"] is True and binding["authorization_header"] is False
            and binding["verifier_sha256"] == sha(content(PUBLICATION, "verifier.py"))
            and binding["anonymous_results_sha256"] == sha(content(PUBLICATION, "results.json"))
            and binding["proof_packet_manifest_sha256"] == sha((root / PREFIX / "manifest.json").read_bytes())
            and binding["original_paper_fully_reproduced"] is False,
            "publication verifier/result/source binding differs")
    counters(binding, {"model_calls": 0, "fresh_Lean_checks": 0, "gpu_trials": 0, "downloaded_files": 59, "downloaded_bytes": 22753879, "observed_exit_code": 0, "prior_failed_source_CI_runs_retained": 1},
             "publication binding execution counters differ")
    summary, run, response = (read(CI, name) for name in ("results.json", "run.json", "jobs.json"))
    jobs = response["jobs"]
    require(summary["status"] == "exact-source-CI-all-21-passed" and summary["source_commit"] == PUBLISHED
            and summary["run_id"] == run["id"] == 43500937594
            and summary["successful_jobs"] == 21 and set(summary["expected_jobs"]) == JOBS
            and run["head_sha"] == PUBLISHED and run["event"] == "push" and run["name"] == "Verify"
            and run["head_branch"] == "reproduction/ptx-matrix-refinement"
            and run["status"] == "completed" and run["conclusion"] == "success"
            and response["total_count"] == len(jobs) == len({j["id"] for j in jobs}) == 21
            and {j["name"] for j in jobs} == JOBS
            and all(j["status"] == "completed" and j["conclusion"] == "success"
                    and j["run_id"] == run["id"] for j in jobs)
            and summary["original_paper_fully_reproduced"] is False, "actual source CI differs")
    counters(summary, {"model_calls": 0, "gpu_trials": 0, "CI_reruns": 0, "successful_jobs": 21,
                       "new_registered_source_certificates": 0, "prior_failed_source_CI_runs_retained": 1}, "source CI execution counters differ")
    report.update(anonymous_publication_files=59, successful_source_CI_jobs=21)
    return report
