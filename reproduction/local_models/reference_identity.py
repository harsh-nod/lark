"""Check equality of the actual HIP/CUDA SDK specifications in Lean on CPU.

Both original SDK blocks remain intact inside separate namespaces. Every Main
checks their twelve existing obligations and a new function-equality theorem.
This makes no model calls, numerical measurements or GPU execution claims.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import certificate, real_backend  # noqa: E402
from reproduction.local_models import full_shape_run as run  # noqa: E402

OBLIGATIONS = ("segmentation_data", "segmentation", "race_free", "segment_equivalence",
               "kernel_eq_spec", "kernel_eq_spec_pre")
TAGS = tuple(f"{backend}.LarkCertificate.{name}"
             for backend in ("Hip", "Cuda") for name in OBLIGATIONS) + ("hip_cuda_spec_eq",)


def log_audits(log, tags=TAGS):
    if "sorry" in log or "error:" in log:
        return False
    for tag in tags:
        no_axioms = re.findall("^" + re.escape(f"'{tag}' does not depend on any axioms")
                               + r"\s*$", log, re.M)
        dependencies = re.findall("^" + re.escape(f"'{tag}' depends on axioms:")
                                  + r"\s*\[([^]]*)\]", log, re.M)
        if len(no_axioms) + len(dependencies) != 1:
            return False
        if dependencies and not {
            name.strip() for name in dependencies[0].split(",") if name.strip()
        } <= certificate.AXIOMS:
            return False
    return True


def main_source(hip_block, cuda_block):
    run.require("set_option" not in hip_block + cuda_block, "Unexpected SDK block option")
    return (
        "import " + run.full_shape.TARGET + "\nset_option maxRecDepth 10000\n"
        "set_option maxHeartbeats 2000000\nnamespace Hip\n" + hip_block +
        "\nend Hip\nnamespace Cuda\n" + cuda_block + "\nend Cuda\n"
        "theorem hip_cuda_spec_eq : @Hip.LarkCertificate.spec = @Cuda.LarkCertificate.spec := by\n"
        "  rfl\n#print axioms hip_cuda_spec_eq\n"
    )


def wrong_operator_refusal(main, log):
    body = main.splitlines().index("  rfl") + 1
    errors = list(re.finditer(r"(?m)^Main\.lean:([0-9]+):[0-9]+: error:", log))
    run.require(errors and all(int(error.group(1)) == body for error in errors),
                "Wrong-operator control failed outside the identity proof")
    run.require(log_audits(log[:errors[0].start()], TAGS[:-1]),
                "Wrong-operator control did not check both original source proofs")
    if "maximum recursion depth has been reached" in log:
        return "fixed-recursion-limit"
    if "maximum number of heartbeats" in log or "maximum heartbeats" in log:
        return "fixed-heartbeat-limit"
    run.require("tactic 'rfl' failed" in log, "Unexpected wrong-operator identity diagnostic")
    return "reflexivity-proof-refused"


def check(output, hip, cuda, hip_name, cuda_name, lean, environment, expected):
    output.mkdir()
    left = hip / "cases" / hip_name
    right = cuda / "cases" / cuda_name
    left_block = (left / "sdk-block.lean.txt").read_text()
    right_block = (right / "sdk-block.lean.txt").read_text()
    main = main_source(left_block, right_block)
    (output / "Main.lean").write_text(main)
    started = time.monotonic()
    try:
        completed = subprocess.run([str(lean), "Main.lean"], cwd=output, env=environment,
                                   text=True, capture_output=True, timeout=180)
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout.decode() if isinstance(error.stdout, bytes) else error.stdout or ""
        stderr = error.stderr.decode() if isinstance(error.stderr, bytes) else error.stderr or ""
        (output / "lean.log").write_text(stdout + stderr + "\nLean timed out; no proof accepted.\n")
        raise ValueError("Specification identity process exceeded the fixed180second cap") from error
    log = completed.stdout + completed.stderr
    (output / "lean.log").write_text(log)
    accepted = completed.returncode == 0 and log_audits(log)
    run.require(accepted is expected, "Unexpected specification identity result: " + str(output))
    rejection = None if expected else wrong_operator_refusal(main, log)
    first = json.loads((left / "request.json").read_text())["source_files"]
    second = json.loads((right / "request.json").read_text())["source_files"]
    left_ref = next(v for k, v in first.items() if k.endswith("/reference.py"))
    right_ref = next(v for k, v in second.items() if k.endswith("/reference.py"))
    row = {
        "hip_case": hip_name, "cuda_case": cuda_name, "accepted": accepted,
        "lean_exit_code": completed.returncode, "seconds": time.monotonic() - started,
        "main_sha256": run.sha(output / "Main.lean"), "log_sha256": run.sha(output / "lean.log"),
        "hip_sdk_block_sha256": run.sha(left / "sdk-block.lean.txt"),
        "cuda_sdk_block_sha256": run.sha(right / "sdk-block.lean.txt"),
        "torch_reference_bytes_identical": left_ref == right_ref,
        "hip_torch_reference_sha256": hashlib.sha256(left_ref.encode()).hexdigest(),
        "cuda_torch_reference_sha256": hashlib.sha256(right_ref.encode()).hexdigest(),
        "rejection_reason": rejection,
        "semantic_counterexample_proved": False,
    }
    run.write(output / "results.json", row)
    return row


def study(hip, cuda, output, lean):
    hip, cuda, output = (Path(p).resolve() for p in (hip, cuda, output))
    run.require(not any((p / ".git").exists() for p in (output, *output.parents)),
                "Study outputs must be outside Git")
    left_sources = run.verify_preparation(hip)
    right_sources = run.verify_preparation(cuda)
    run.require(run.sha(hip / "manifest.json") == run.PREPARATION_SHA256
                and run.sha(cuda / "manifest.json") == run.CUDA_PREPARATION_SHA256,
                "The two independently pinned source backends are required")
    output.mkdir(parents=True, exist_ok=False)
    sources = {}
    for prepared, manifest in ((hip, left_sources), (cuda, right_sources)):
        for name, digest in manifest.items():
            run.require(name not in sources or sources[name] == digest, "Conflicting shared source")
            sources[name] = digest
            path = output / "source" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((prepared / "source" / name).read_bytes())
    name = "reproduction/local_models/reference_identity.py"
    (output / "source" / name).write_bytes(Path(__file__).read_bytes())
    sources[name] = run.sha(Path(__file__))
    run.write(output / "source-manifest.json", dict(sorted(sources.items())))
    libraries = run.full_shape.benchmark.reference_libraries(run.full_shape.references)
    cache, environment = real_backend.prepare(libraries, str(lean), 600, target=run.full_shape.TARGET)
    report = {
        "schema": 1, "status": "reference-identity-checks-in-progress",
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "hip_preparation_manifest_sha256": run.PREPARATION_SHA256,
        "cuda_preparation_manifest_sha256": run.CUDA_PREPARATION_SHA256,
        "driver_sha256": run.sha(Path(__file__)), "lean_binary_sha256": run.sha(lean),
        "source_manifest_sha256": run.sha(output / "source-manifest.json"),
        "source_checked_import_cache": str(cache), "cold_import_rebuild_claimed": False,
        "limits": run.full_shape.LIMITS, "axiom_audits_per_positive_main": len(TAGS),
        "model_calls": 0, "gpu_trials": 0, "new_registered_certificates": 0,
        "new_numerical_samples": 0, "original_paper_fully_reproduced": False, "cases": [],
        "scope": "Actual HIP/CUDA SDK specification-function equality at the17 existing shapes for every scalar interpretation/input. Existing source proofs checked alongside each identity. No CUDA execution, NVIDIA measurement, IEEE-error theorem, model trial or numerical rerun.",
    }
    run.write(output / "results.json", report)
    (output / "cases").mkdir()
    for name, *_ in run.full_shape.benchmark.CASES:
        result = check(output / "cases" / name, hip, cuda, name, name, lean, environment, True)
        run.require(result["torch_reference_bytes_identical"], "The paired Torch references differ")
        report["cases"].append(result)
        run.write(output / "results.json", report)
        print(json.dumps({"case": name, "specification_function_equality": True}), flush=True)
    control = check(output / "wrong-operator-control", hip, cuda, "relu", "gelu", lean,
                    environment, False)
    report.update(status="all-seventeen-hip-cuda-specifications-identical-and-control-refused",
                  specification_identity_theorems=len(report["cases"]),
                  axiom_audit_occurrences=len(report["cases"]) * len(TAGS),
                  wrong_operator_control=control)
    run.write(output / "results.json", report)
    run.write(output / "manifest.json", {
        str(p.relative_to(output)): run.sha(p) for p in sorted(output.rglob("*")) if p.is_file()})
    print(json.dumps({"status": report["status"], "specification_identity_theorems": 17,
                      "model_calls": 0, "gpu_trials": 0}))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("hip-prepared", "cuda-prepared", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    study(args.hip_prepared, args.cuda_prepared, args.output,
          Path(certificate.lean_binary(str(args.lean))))


if __name__ == "__main__":
    main()
