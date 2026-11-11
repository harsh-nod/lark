"""Recompute every finite double reference and audit both in-out output streams."""

import argparse
import hashlib
import json
from pathlib import Path


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify(root, hashes):
    for name, digest in hashes.items():
        path = (root / name).resolve()
        if not path.is_relative_to(root.resolve()) or sha(path) != digest:
            raise ValueError("File binding differs: " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = args.input.resolve()
    if args.output.exists():
        raise ValueError("Fresh audit output required")
    verify(data, json.loads((data / "manifest.json").read_text())["files"])
    metadata = json.loads((data / "dataset.json").read_text())
    if (metadata["source_certificates"] != 0 or metadata["whole_kernel_execution_proved"]
            or metadata["actual_trace_classification_proved"] or metadata["original_paper_fully_reproduced"]):
        raise ValueError("Unsupported development-evidence completion claim")
    if metadata["atol"] != .002 or metadata["rtol"] != .002:
        raise ValueError("Numerical tolerance differs")
    expected_records = [{"rows": c["rows"], **t, "elements_per_buffer": c["elements"]}
                        for c in metadata["cases"] for t in c["trials"]]
    if [c["rows"] for c in metadata["cases"]] != [1, 3, 64, 255] or len(expected_records) != 24:
        raise ValueError("Numerical cohort differs")
    import numpy as np

    names = ("adapted-input", "adapted-residual", "upstream-input", "upstream-residual")
    total = metadata["outputs_per_method_per_buffer"]
    inputs = {name: np.memmap(data / (name + ".bin"), dtype="<f2", mode="r")
              for name in ("input", "residual", "weight", "expected-residual")}
    saved_reference = np.memmap(data / "expected-input.bin", dtype="<f4", mode="r")
    hosts, streams = [], []
    for host in args.host:
        host = host.resolve()
        verify(host, json.loads((host / "manifest.json").read_text()))
        report = json.loads((host / "results.json").read_text())
        if (report["input_manifest_sha256"] != sha(data / "manifest.json")
                or report["runner_sha256"] != sha(data / "run_gpu.py")
                or report["trials"] != 24 or report["launches"] != 48
                or report["output_elements_per_method_per_buffer"] != total
                or report["warp"] != 64 or report["block"] != 1024
                or report["source_certificates"] != 0 or report["whole_kernel_execution_proved"]
                or report["actual_trace_classification_proved"] or report["ieee_equivalence_proved"]
                or report["original_paper_fully_reproduced"] or report["original_nvidia_kernel_executed"]):
            raise ValueError("Runtime binding or scope differs")
        if len(report["cases"]) != len(expected_records):
            raise ValueError("Trial record missing")
        for wanted, got in zip(expected_records, report["cases"]):
            if (any(got[k] != v for k, v in wanted.items())
                    or not got["all_allocation_guards_unchanged"] or not got["weight_unchanged"]):
                raise ValueError("Runtime guard/trial record differs")
        for name in names:
            if (host / (name + ".bin")).stat().st_size != total * 2:
                raise ValueError("Truncated or enlarged output stream")
            if sha(host / (name + ".bin")) != report["output_sha256"][name]:
                raise ValueError("Output report binding differs")
        streams.append({name: np.memmap(host / (name + ".bin"), dtype="<f2", mode="r") for name in names})
        hosts.append({"directory": host.name, "device": report["device"], "trials": 24,
                      "compiler_inputs": report["compiler_inputs"], "report_sha256": sha(host / "results.json"),
                      "normalized_comparisons": 0, "residual_bit_comparisons": 0,
                      "tolerance_failures": 0, "residual_bit_failures": 0,
                      "normalized_max_abs_error": 0., "adapted_vs_upstream_input_bit_differences": 0,
                      "adapted_vs_upstream_residual_bit_differences": 0,
                      "normalized_signed_zero_differences": 0, "normalized_other_bit_differences": 0,
                      "normalized_nonzero_sign_disagreements": 0, "normalized_max_magnitude_ulp_difference": 0,
                      "normalized_max_method_abs_difference": 0., "bit_difference_details": []})
    reference_cases = 0
    for case in metadata["cases"]:
        rows, n = case["rows"], case["elements"]
        for trial in case["trials"]:
            offset = trial["offset_elements"]
            sl = slice(offset, offset + n)
            woff = trial["weight_offset_bytes"] // 2
            a = inputs["input"][sl].astype(np.float64)
            residual = inputs["residual"][sl].astype(np.float64)
            weight = inputs["weight"][woff:woff + 16384].astype(np.float64)
            if not all(np.isfinite(x).all() for x in (a, residual, weight)):
                raise ValueError("Nonfinite prepared operand")
            x = (a + residual).reshape(rows, 16384)
            expected = (x / np.sqrt((x * x).mean(axis=1, keepdims=True) + 1e-5) * weight).reshape(-1)
            residual_bits = (a.astype(np.float32) + residual.astype(np.float32)).astype("<f2").view("<u2")
            if (not np.isfinite(expected).all()
                    or not np.array_equal(expected.astype("<f4").view("<u4"), saved_reference[sl].view("<u4"))
                    or not np.array_equal(residual_bits, inputs["expected-residual"][sl].view("<u2"))):
                raise ValueError("Recomputed CPU reference differs from prepared data")
            for host, values in zip(hosts, streams):
                for method in ("adapted", "upstream"):
                    got = values[method + "-input"][sl].astype(np.float64)
                    if not np.isfinite(got).all():
                        raise ValueError("Nonfinite normalized output")
                    errors = np.abs(got - expected)
                    failures = ~np.isfinite(got) | (errors > .002 + .002 * np.abs(expected))
                    host["normalized_comparisons"] += n
                    host["residual_bit_comparisons"] += n
                    host["tolerance_failures"] += int(np.count_nonzero(failures))
                    host["residual_bit_failures"] += int(np.count_nonzero(values[method + "-residual"][sl].view("<u2") != residual_bits))
                    host["normalized_max_abs_error"] = max(host["normalized_max_abs_error"], float(errors.max()))
                for buffer in ("input", "residual"):
                    host["adapted_vs_upstream_" + buffer + "_bit_differences"] += int(np.count_nonzero(
                        values["adapted-" + buffer][sl].view("<u2") != values["upstream-" + buffer][sl].view("<u2")))
                a_bits = values["adapted-input"][sl].view("<u2")
                b_bits = values["upstream-input"][sl].view("<u2")
                different = a_bits != b_bits
                signed_zero = different & ((a_bits & 0x7fff) == 0) & ((b_bits & 0x7fff) == 0)
                other = different & ~signed_zero
                zeros, others = int(np.count_nonzero(signed_zero)), int(np.count_nonzero(other))
                sign_disagreements = int(np.count_nonzero(other & ((a_bits & 0x8000) != (b_bits & 0x8000))))
                ulps = (int(np.max(np.abs((a_bits[other] & 0x7fff).astype(np.int32)
                                         - (b_bits[other] & 0x7fff).astype(np.int32)))) if others else 0)
                method_error = float(np.max(np.abs(values["adapted-input"][sl].astype(np.float64)
                                                   - values["upstream-input"][sl].astype(np.float64))))
                host["normalized_signed_zero_differences"] += zeros
                host["normalized_other_bit_differences"] += others
                host["normalized_nonzero_sign_disagreements"] += sign_disagreements
                host["normalized_max_magnitude_ulp_difference"] = max(host["normalized_max_magnitude_ulp_difference"], ulps)
                host["normalized_max_method_abs_difference"] = max(host["normalized_max_method_abs_difference"], method_error)
                host["bit_difference_details"].append({"rows": rows, "trial": trial["trial"], "label": trial["label"],
                                                      "signed_zero_differences": zeros, "other_bit_differences": others,
                                                      "nonzero_sign_disagreements": sign_disagreements,
                                                      "max_magnitude_ulp_difference": ulps, "max_abs_difference": method_error})
            reference_cases += 1
    output_hashes = {name: [sha(host / (name + ".bin")) for host in args.host] for name in names}
    failures = sum(h["tolerance_failures"] + h["residual_bit_failures"] for h in hosts)
    result = {
        "schema": 1, "status": "passed" if not failures else "failed", "hosts": hosts,
        "fresh_cpu_double_reference_cases": reference_cases,
        "normalized_comparisons": sum(h["normalized_comparisons"] for h in hosts),
        "residual_bit_comparisons": sum(h["residual_bit_comparisons"] for h in hosts),
        "tolerance_failures": sum(h["tolerance_failures"] for h in hosts),
        "residual_bit_failures": sum(h["residual_bit_failures"] for h in hosts),
        "cross_host_streams_identical": {name: len(set(hashes)) == 1 for name, hashes in output_hashes.items()},
        "output_sha256": output_hashes, "input_manifest_sha256": sha(data / "manifest.json"),
        "source_kernel_sha256": sha(data / "kernel.hip"), "auditor_sha256": sha(Path(__file__)),
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "ieee_equivalence_proved": False,
        "floating_point_error_bound_proved": False, "original_paper_fully_reproduced": False,
        "model_calls": 0,
        "scope": "Finite independent HIP adaptation checks: float64 numerical tolerance for normalized input, exact FP32-add-to-FP16 bits for residual, both methods/hosts. The comparison retains the selected upstream template body with replaced HIP helpers. Not an original-paper result or complete source certificate.",
    }
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "fresh_cpu_double_reference_cases", "normalized_comparisons", "residual_bit_comparisons", "tolerance_failures", "residual_bit_failures")}), flush=True)
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
