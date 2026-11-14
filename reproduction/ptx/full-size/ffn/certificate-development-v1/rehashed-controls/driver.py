"""Retain and reject coherently rehashed false full-FFN proof recordings."""

import argparse
import copy
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_ffn_certificate as checker  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("recording", "output", "lean"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    output, original = checker.fresh_output(args.output), args.recording.resolve()
    checker.check_inventory(original)
    baseline = checker.read(original / "results.json")
    checker.require(baseline["source_bound_proof_accepted"] is True, "Verified positive recording required")
    output.mkdir(parents=True)
    (output / "driver.py").write_bytes(Path(__file__).read_bytes())
    changes = (
        ("boolean-schema", ["schema"], True),
        ("boolean-development-count", ["source_bound_development_proofs"], True),
        ("floating-module-count", ["owned_Lean_modules_freshly_compiled"], 14.0),
        ("NVIDIA-execution-overclaim", ["nvidia_execution"], True),
        ("paper-reproduction-overclaim", ["original_paper_fully_reproduced"], True),
        ("legacy-certificate-overclaim", ["new_registered_source_certificates"], 1),
        ("paid-model-call-overclaim", ["model_calls"], 1),
        ("heartbeat-cap-increased", ["limits", "maxHeartbeats"], 4000000),
        ("recursion-cap-increased", ["limits", "maxRecDepth"], 20000),
        ("per-process-cap-increased", ["limits", "per_Lean_process_seconds"], 360),
        ("source-build-cap-increased", ["limits", "source_import_build_seconds"], 1200),
        ("stack-cap-increased", ["original_stack_limits", 0], 16777216),
        ("down-CUDA-fuel-shortened", ["stages", 1, "unchanged_CUDA_contract_fuel", 0], 1030),
        ("boolean-up-CUDA-fuel", ["stages", 0, "unchanged_CUDA_contract_fuel", 1], True),
        ("boolean-down-block-size", ["stages", 1, "launch", "block"], True),
        ("half-up-launch", ["stages", 0, "launch", "grid"], 32768),
        ("shortened-down-program", ["stages", 1, "PTX_instructions"], 170),
        ("launch-order-reversed", ["host_launch_order"], ["down", "up"]),
        ("intermediate-rebound", ["shared_intermediate", "name"], "fresh_reference_hidden"),
        ("intermediate-dtype-changed", ["shared_intermediate", "dtype"], "float32"),
        ("claimed-owned-cache-reuse", ["old_owned_olean_cache_used"], True),
        ("module-roster-shortened", None, None),
        ("missing-pipeline-axiom-audit", None, None),
        ("missing-library-axiom-audit", None, None),
        ("coherently-rehashed-reference-AST", None, None),
        ("coherently-rehashed-translation", None, None),
        ("coherently-rehashed-Main", None, None),
        ("coherently-rehashed-captured-Python", None, None),
        ("coherently-rehashed-captured-Lean", None, None),
        ("coherently-rehashed-forbidden-axiom-log", None, None),
        ("coherently-rehashed-down-contract", None, None),
    )
    results = []
    for label, keys, value in changes:
        case = output / label
        recording = case / "recording"
        shutil.copytree(original, recording)
        report = copy.deepcopy(baseline)
        if keys:
            field = report
            for key in keys[:-1]:
                field = field[key]
            field[keys[-1]] = value
        elif label == "module-roster-shortened":
            report["module_checks"].pop()
        elif label == "missing-pipeline-axiom-audit":
            report["axiom_audits"].pop("LarkPtxFfnCertificate.complete_pipeline")
        elif label == "missing-library-axiom-audit":
            report["library_axiom_audits"].pop("LarkPtxFeedForward.Pipeline.actual_intermediate_shared")
        elif label == "coherently-rehashed-reference-AST":
            tree = checker.read(recording / "reference-ast.json")
            assert tree[1][1][1][0] == "toHalf"
            tree[1][1][1][0] = "fromHalf"
            checker.write(recording / "reference-ast.json", tree)
            report["reference_ast_sha256"] = checker.sha((recording / "reference-ast.json").read_bytes())
        elif label == "coherently-rehashed-translation":
            tree = checker.read(recording / "translation.json")
            tree[1]["instructions"][-1] = ["barrier"]
            checker.write(recording / "translation.json", tree)
        elif label == "coherently-rehashed-Main":
            path = recording / "Main.lean"
            text = path.read_text()
            assert text.count("by decide") == 2
            path.write_text(text.replace("by decide", "by rfl", 1))
            report["main_sha256"] = checker.sha(path.read_bytes())
        elif label in ("coherently-rehashed-captured-Python", "coherently-rehashed-captured-Lean"):
            name = ("python/ptx_ffn_certificate.py" if label.endswith("Python")
                    else "lean/Lark/PtxFeedForwardPipeline.lean")
            path = recording / "owned-sources" / name
            suffix = ('\nraise AssertionError("captured Python executed")\n' if label.endswith("Python")
                      else "\naxiom untrustedCapturedFalse : False\n")
            path.write_text(path.read_text() + suffix)
            bindings = checker.read(recording / "source-bindings.json")
            bindings[name] = checker.sha(path.read_bytes())
            checker.write(recording / "source-bindings.json", bindings)
            report["source_bindings_sha256"] = checker.sha((recording / "source-bindings.json").read_bytes())
        elif label == "coherently-rehashed-forbidden-axiom-log":
            path = recording / "Main.log"
            text = path.read_text()
            assert "Quot.sound" in text
            path.write_text(text.replace("Quot.sound", "sorryAx", 1))
            report["main_check"]["log_sha256"] = checker.sha(path.read_bytes())
        elif label == "coherently-rehashed-down-contract":
            path = recording / "down/contract.json"
            task = checker.read(path)
            task["fuel"][0] = 1030
            checker.write(path, task)
            report["input_bindings"]["down/contract.json"] = checker.sha(path.read_bytes())
        else:
            raise AssertionError(label)
        checker.write(recording / "results.json", report)
        checker.manifest(recording)
        destination = case / "unexpected-fresh-replay"
        try:
            checker.check_export(recording, destination, args.lean)
        except Refusal as error:
            result = {"name": label, "status": "rejected-before-fresh-Lean-work",
                      "code": error.code, "detail": error.detail,
                      "output_created": destination.exists(),
                      "complete_false_recording_manifest_sha256": checker.sha((recording / "manifest.json").read_bytes())}
            checker.require(not destination.exists(), "Control unexpectedly created a fresh build: " + label)
        else:
            raise AssertionError("False recording unexpectedly accepted: " + label)
        checker.write(case / "results.json", result)
        checker.manifest(case)
        results.append(result)
        checker.write(output / "partial-results.json", results)
    report = {"status": "all31-coherently-rehashed-FFN-controls-rejected", "checks": results,
              "negative_controls": len(changes), "fresh_Lean_checks": 0,
              "all_false_payloads_retained": True, "GPU_trials": 0, "model_calls": 0,
              "source_bound_proofs_added": 0, "new_registered_source_certificates": 0,
              "original_paper_fully_reproduced": False}
    checker.write(output / "results.json", report)
    checker.manifest(output)
    print(json.dumps({key: report[key] for key in ("status", "negative_controls", "fresh_Lean_checks")}), flush=True)


if __name__ == "__main__":
    main()
