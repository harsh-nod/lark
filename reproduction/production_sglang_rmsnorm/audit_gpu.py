"""Independently recompute dense CPU references and audit all frozen GPU outputs."""

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def verify(root, hashes):
    for name, expected in hashes.items():
        path = (root / name).resolve()
        if not path.is_relative_to(root) or sha(path) != expected:
            raise ValueError("File binding differs: " + name)


def scope(report, *, runtime=False):
    wanted = {"source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_trace_classification_proved": False,
              "source_reference_equality_proved": False, "model_calls": 0,
              "original_paper_fully_reproduced": False}
    if runtime:
        wanted.update(ieee_equivalence_proved=False, original_nvidia_kernel_executed=False)
    claims = {k for k in report if k.endswith(("_proved", "_certificates", "_fully_reproduced"))
              or k in ("model_calls", "original_nvidia_kernel_executed")}
    if (claims != set(wanted)
            or any(type(report.get(k)) is not type(v) or report[k] != v for k, v in wanted.items())):
        raise ValueError("Unsupported numerical-evidence proof/completion scope")


def compiler_capture(host, data):
    inventory = json.loads((host / "compiler-inputs.json").read_text())
    for filename in ("kernel_original.hip", "kernel_fixed.hip", "driver.hip"):
        candidates = [digest for name, digest in inventory.items() if name.endswith("/" + filename)]
        if candidates != [sha(data / filename)]:
            raise ValueError("Compiler source does not match frozen " + filename)
    seen = set()
    with tarfile.open(host / "compiler-inputs.tar.gz") as archive:
        for entry in archive:
            key = "/" + entry.name
            if (not entry.isfile() or key not in inventory or key in seen
                    or hashlib.sha256(archive.extractfile(entry).read()).hexdigest() != inventory[key]):
                raise ValueError("Compiler capture differs")
            seen.add(key)
    if seen != set(inventory):
        raise ValueError("Incomplete compiler capture")
    return len(inventory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if len(args.host) != 2 or len({p.resolve() for p in args.host}) != 2:
        raise ValueError("Two distinct host packets are required for this paired study")
    data = args.input.resolve()
    if args.output.exists():
        raise ValueError("Fresh numerical audit output required")
    verify(data, json.loads((data / "manifest.json").read_text())["files"])
    if sha(data / "audit_gpu.py") != sha(Path(__file__)):
        raise ValueError("Auditor differs from the frozen numerical input packet")
    metadata = json.loads((data / "dataset.json").read_text())
    scope(metadata)
    if metadata.get("methods") != ["original", "fixed", "upstream"]:
        raise ValueError("Numerical source method cohort differs")
    if metadata["atol"] != .002 or metadata["rtol"] != .002:
        raise ValueError("Fixed numerical tolerance differs")
    if ([c["rows"] for c in metadata["cases"]] != [1, 3, 64, 255]
            or any(type(c["rows"]) is not int for c in metadata["cases"])):
        raise ValueError("Numerical row cohort differs")
    labels = ["seeded-normal", "signed-zero", "constant", "structured-dyadic",
              "half-rounding-and-subnormals", "mixed-magnitudes"]
    offset, weight_offset, expected_records = 0, 0, []
    for case in metadata["cases"]:
        n = case["rows"] * 16384
        if case["elements"] != n or len(case["trials"]) != 6:
            raise ValueError("Numerical trial cohort differs")
        for trial, wanted_label in zip(case["trials"], labels):
            if (any(type(trial[k]) is not int for k in ("trial", "offset_elements", "weight_offset_bytes"))
                    or trial["trial"] != len(expected_records) % 6 or trial["label"] != wanted_label
                    or trial["offset_elements"] != offset or trial["weight_offset_bytes"] != weight_offset):
                raise ValueError("Numerical stream layout differs")
            expected_records.append({"rows": case["rows"], **trial, "elements": n})
            offset += n
            weight_offset += 16384 * 2
    total = metadata["outputs_per_method"]
    if total != offset or len(expected_records) != 24:
        raise ValueError("Numerical output count differs")
    if (data / "input.bin").stat().st_size != total * 2 or (data / "weight.bin").stat().st_size != weight_offset:
        raise ValueError("Input stream size differs")
    upstream = (data / "upstream/python/sglang/kernels/jit/csrc/elementwise/rmsnorm.cuh").read_text()
    signature = upstream.index("void rmsnorm_cta_double(")
    start = upstream.rindex("template <", 0, signature)
    begin = upstream.index("{", start)
    depth, end = 1, begin + 1
    while depth:
        depth += (upstream[end] == "{") - (upstream[end] == "}")
        end += 1
    body = upstream[start:end]
    if (hashlib.sha256(body.encode()).hexdigest() != metadata["upstream_template_body_sha256"]
            or (data / "driver.hip").read_text().count(body) != 1):
        raise ValueError("Pinned comparison body differs")

    import numpy as np
    import torch
    torch.set_num_threads(1)
    operands = {name: np.memmap(data / (name + ".bin"), dtype="<f2", mode="r")
                for name in ("input", "weight")}
    hosts, streams = [], []
    for path in args.host:
        host = path.resolve()
        verify(host, json.loads((host / "manifest.json").read_text()))
        report = json.loads((host / "results.json").read_text())
        scope(report, runtime=True)
        if (report["status"] != "runtime-checks-passed-pending-independent-numerical-audit"
                or report["input_manifest_sha256"] != sha(data / "manifest.json")
                or report["runner_sha256"] != sha(data / "run_gpu.py")
                or report["binary_sha256"] != sha(host / "driver.so")
                or report["trials"] != 24 or report["launches"] != 72
                or report["output_elements_per_method"] != total
                or report["warp"] != 64 or report["block"] != 1024 or report["shared_bytes"] != 128
                or not report["architecture"].startswith("gfx950")
                or report.get("methods") != ["original", "fixed", "upstream"]
                or report["comparison_template_body_retained"] is not True
                or report["comparison_helpers_replaced_for_hip"] is not True):
            raise ValueError("Runtime source/geometry binding differs")
        if len(report["cases"]) != len(expected_records):
            raise ValueError("Runtime trial missing")
        for wanted, got in zip(expected_records, report["cases"]):
            if (any(got[k] != v for k, v in wanted.items())
                    or any(got[k] is not True for k in
                           ("all_allocation_guards_unchanged", "input_unchanged", "weight_unchanged"))):
                raise ValueError("Runtime guard/trial record differs")
        guard = json.loads((host / "memory-guard.json").read_text())
        if (guard.get("minimum_free_fraction") != .98 or guard.get("busy_percent") != 0
                or not isinstance(guard.get("free_bytes"), int)
                or not isinstance(guard.get("total_bytes"), int)
                or guard["total_bytes"] <= 0 or guard["free_bytes"] < .98 * guard["total_bytes"]):
            raise ValueError("Idle GPU guard differs")
        count = compiler_capture(host, data)
        if count != report["compiler_inputs"]:
            raise ValueError("Compiler input count differs")
        for name in ("original", "fixed", "upstream"):
            if ((host / (name + ".bin")).stat().st_size != total * 2
                    or sha(host / (name + ".bin")) != report["output_sha256"][name]):
                raise ValueError("Output stream binding differs")
        streams.append({name: np.memmap(host / (name + ".bin"), dtype="<f2", mode="r")
                        for name in ("original", "fixed", "upstream")})
        hosts.append({"directory": host.name, "hostname": report["hostname"],
                      "device": report["device"], "trials": 24,
                      "report_sha256": sha(host / "results.json"), "compiler_inputs": count,
                      "cpu_float64_compared_values": 0, "torch_fp32_bit_comparisons": 0,
                      "tolerance_failures": 0, "nonfinite_outputs": 0,
                      "max_abs_error": 0., "method_pair_bit_differences": {"original_fixed": 0, "original_upstream": 0, "fixed_upstream": 0},
                      "torch_fp32_bit_differences": 0, "rounding_details": []})
    reference_cases = 0
    for case in metadata["cases"]:
        rows, n = case["rows"], case["elements"]
        for trial in case["trials"]:
            offset = trial["offset_elements"]
            sl = slice(offset, offset + n)
            woff = trial["weight_offset_bytes"] // 2
            raw_input = operands["input"][sl]
            raw_weight = operands["weight"][woff:woff + 16384]
            x = raw_input.astype(np.float64).reshape(rows, 16384)
            weight = raw_weight.astype(np.float64)
            if not np.isfinite(x).all() or not np.isfinite(weight).all():
                raise ValueError("Nonfinite operand")
            expected = (x / np.sqrt((x * x).mean(axis=1, keepdims=True) + 1e-5) * weight).reshape(-1)
            tx = torch.from_numpy(np.array(raw_input, dtype=np.float32)).reshape(rows, 16384)
            tw = torch.from_numpy(np.array(raw_weight, dtype=np.float32))
            torch_expected = (tx * torch.rsqrt((tx * tx).mean(dim=1, keepdim=True) + 1e-5)
                              * tw).half().numpy().astype("<f2", copy=False).reshape(-1)
            if (not np.isfinite(expected).all() or not np.isfinite(torch_expected).all()
                    or hashlib.sha256(expected.astype("<f8").tobytes()).hexdigest() != trial["cpu_float64_reference_sha256"]
                    or hashlib.sha256(torch_expected.tobytes()).hexdigest() != trial["torch_fp32_rounded_reference_sha256"]):
                raise ValueError("Recomputed CPU reference differs from frozen reference hash")
            for host, values in zip(hosts, streams):
                details = {"rows": rows, "trial": trial["trial"], "label": trial["label"],
                           "torch_fp32_bit_differences": {}}
                for method in ("original", "fixed", "upstream"):
                    got = values[method][sl].astype(np.float64)
                    finite = np.isfinite(got)
                    errors = np.abs(got - expected)
                    failures = ~finite | (errors > .002 + .002 * np.abs(expected))
                    different = int(np.count_nonzero(values[method][sl].view("<u2") != torch_expected.view("<u2")))
                    host["cpu_float64_compared_values"] += n
                    host["torch_fp32_bit_comparisons"] += n
                    host["tolerance_failures"] += int(np.count_nonzero(failures))
                    host["nonfinite_outputs"] += int(np.count_nonzero(~finite))
                    host["max_abs_error"] = max(host["max_abs_error"], float(errors[finite].max(initial=0)))
                    host["torch_fp32_bit_differences"] += different
                    details["torch_fp32_bit_differences"][method] = different
                pair_differences = {}
                for left, right in (("original", "fixed"), ("original", "upstream"), ("fixed", "upstream")):
                    key = left + "_" + right
                    differences = int(np.count_nonzero(values[left][sl].view("<u2") != values[right][sl].view("<u2")))
                    host["method_pair_bit_differences"][key] += differences
                    pair_differences[key] = differences
                details["method_pair_bit_differences"] = pair_differences
                if any(pair_differences.values()) or any(details["torch_fp32_bit_differences"].values()):
                    host["rounding_details"].append(details)
            reference_cases += 1
    result = {
        "schema": 1, "status": "passed" if all(h["tolerance_failures"] == 0 for h in hosts) else "failed",
        "hosts": hosts, "reference_cases": reference_cases, "atol": .002, "rtol": .002,
        "cpu_float64_compared_values": sum(h["cpu_float64_compared_values"] for h in hosts),
        "torch_fp32_bit_comparisons": sum(h["torch_fp32_bit_comparisons"] for h in hosts),
        "tolerance_failures": sum(h["tolerance_failures"] for h in hosts),
        "method_pair_bit_differences": {key: sum(h["method_pair_bit_differences"][key] for h in hosts)
                                        for key in ("original_fixed", "original_upstream", "fixed_upstream")},
        "torch_fp32_bit_differences": sum(h["torch_fp32_bit_differences"] for h in hosts),
        "all_cross_host_output_streams_bit_identical": all(
            sha(args.host[0] / (name + ".bin")) == sha(host / (name + ".bin"))
            for host in args.host[1:] for name in ("original", "fixed", "upstream")),
        "input_manifest_sha256": sha(data / "manifest.json"), "auditor_sha256": sha(Path(__file__)),
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "source_reference_equality_proved": False,
        "ieee_equivalence_proved": False, "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "cpu_float64_compared_values", "tolerance_failures",
                                           "method_pair_bit_differences", "torch_fp32_bit_differences")}), flush=True)
    if result["status"] != "passed":
        raise ValueError("Numerical tolerance failed")


if __name__ == "__main__":
    main()
