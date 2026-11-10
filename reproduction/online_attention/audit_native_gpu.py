"""Recompute paired native FP16/upstream FP32 comparisons from frozen inputs.

The audit checks finite numerical evidence, not universal source execution,
race freedom, IEEE equivalence or the authors' original production adaptation.
"""

import argparse
import hashlib
import json
from pathlib import Path
import tarfile

from audit_gpu import manifest, require, sha


def check(data, hosts):
    import numpy as np
    import torch

    torch.set_num_threads(1)
    manifest(data)
    meta = json.loads((data / "dataset.json").read_text())
    flags = ("whole_kernel_execution_proved", "actual_trace_classification_proved",
             "ieee_equivalence_proved", "original_paper_fully_reproduced")
    require(all(meta[k] is False for k in flags), "Unsupported formal or original-paper claim")
    require(meta["source_certificates"] == 0 and meta["model_calls"] == 0, "Unsupported count")
    require([meta[k] for k in ("adapted_atol", "adapted_rtol", "upstream_atol", "upstream_rtol")] == [0.002, 0.002, 0.0001, 0.0002], "Tolerance differs")
    require(sha(data / "kernel.hip") == meta["native_source_sha256"], "Native source differs")
    source = (data / "flash.cu").read_text()
    body = source[source.index("__global__"):source.index("\ntorch::Tensor forward(")]
    require(body.encode() == (data / "upstream_context.cuh").read_bytes(), "Upstream extraction differs")
    require(hashlib.sha256(body.encode()).hexdigest() == meta["upstream_definition_sha256"], "Upstream definition hash differs")
    streams = {n: (data / (n + ".bin")).read_bytes() for n in ("query", "key", "value", "qf", "kf", "vf", "expected")}
    families = {"seeded-normal", "zero-scores", "constant-scores", "alternating", "sharp", "large-common-score-shift"}
    cases = meta["cases"]
    require(len(cases) == 12 and {(c["groups"], c["family"]) for c in cases} == {(g, f) for g in (1, 3) for f in families}, "Case coverage differs")
    count = 0
    references = []
    for case in cases:
        n, offset = case["elements"], case["offset_elements"]
        require(offset == count and n == case["groups"] * 32768
                and case["n"] == 128 and case["d"] == 256 and case["tile"] == 32
                and case["grid"] == case["groups"] and case["block"] == 32, "Case extent differs")
        tensors = []
        for name, promoted in (("query", "qf"), ("key", "kf"), ("value", "vf")):
            h = np.frombuffer(streams[name], dtype="<f2", count=n, offset=offset * 2).copy()
            require(h.astype("<f4").tobytes() == streams[promoted][offset * 4:(offset + n) * 4], "Input promotion differs")
            tensors.append(torch.from_numpy(h.reshape(case["groups"], 128, 256)).double())
        q, k, v = tensors
        score = (q @ k.transpose(1, 2)) / 16
        require(float(score.min()) == case["reference_score_min"] and float(score.max()) == case["reference_score_max"], "Score range differs")
        expected = (score.softmax(dim=2) @ v).numpy().astype("<f8").tobytes()
        require(expected == streams["expected"][offset * 8:(offset + n) * 8], "Fresh CPU reference differs")
        references.append(np.frombuffer(expected, dtype="<f8"))
        count += n
    require(all(len(v) == count * (8 if k == "expected" else 4 if len(k) == 2 else 2) for k, v in streams.items()), "Stream extent differs")
    summaries, hashes = [], {"adapted": [], "upstream": []}
    for host in hosts:
        manifest(host)
        report = json.loads((host / "results.json").read_text())
        require(all(report[k] is False for k in flags), "Unsupported formal or original-paper claim")
        require(report["source_certificates"] == 0 and report["model_calls"] == 0, "Unsupported count")
        require(report["input_manifest_sha256"] == sha(data / "manifest.json"), "Input binding differs")
        require(report["warp"] == 64 and report["native_block"] == 32 and report["shared_per_block"] >= 102400, "Native launch differs")
        guard = json.loads((host / "memory-guard.json").read_text())
        require(guard["minimum_free_fraction"] == 0.98 and guard["free_bytes"] >= 0.98 * guard["total_bytes"], "Device memory guard failed")
        headers = json.loads((host / "compiler-inputs.json").read_text())
        with tarfile.open(host / "compiler-inputs.tar.gz") as archive:
            members = archive.getmembers()
            require(all(m.isfile() for m in members) and len(members) == len(headers)
                    and {m.name for m in members} == {n.lstrip("/") for n in headers}, "Compiler capture inventory differs")
            for member in members:
                require(hashlib.sha256(archive.extractfile(member).read()).hexdigest() == headers["/" + member.name], "Compiler input differs")
            for name in ("kernel.hip", "native_driver.hip", "fp32_driver.hip", "upstream_context.cuh"):
                matches = [m for m in members if m.name.endswith("/" + name)]
                require(len(matches) == 1 and archive.extractfile(matches[0]).read() == (data / name).read_bytes(), "Compiled source differs: " + name)
        require(report["compiler_input_files"] == len(headers), "Compiler capture count differs")
        require(len(report["cases"]) == len(cases), "Recorded case count differs")
        raw = {name: (host / (name + ".bin")).read_bytes() for name in ("adapted", "upstream")}
        require(len(raw["adapted"]) == count * 2 and len(raw["upstream"]) == count * 4, "Output extent differs")
        maxima = {"adapted": 0.0, "upstream": 0.0}
        differences = 0
        for case, recorded, reference in zip(cases, report["cases"], references):
            require(all(recorded[k] == v for k, v in case.items()), "Recorded case differs")
            require(recorded["paired_output_values"] == case["elements"] and recorded["cpu_reference_comparisons"] == 2 * case["elements"], "Recorded case count differs")
            arrays = {}
            for label, size, dtype in (("adapted", 2, "<f2"), ("upstream", 4, "<f4")):
                values = np.frombuffer(raw[label], dtype=dtype, count=case["elements"], offset=case["offset_elements"] * size)
                arrays[label] = values
                error = np.abs(values.astype(np.float64) - reference)
                failed = int(np.count_nonzero(~np.isfinite(values) | ~np.isfinite(reference) | (error > meta[label + "_atol"] + meta[label + "_rtol"] * np.abs(reference))))
                require(failed == 0 and recorded[label + "_numerical_failures"] == 0, "Numerical tolerance failure: " + label)
                maximum = float(error.max())
                require(recorded[label + "_max_abs_error"] == maximum, "Recorded error differs")
                maxima[label] = max(maxima[label], maximum)
            differences += int(np.count_nonzero(arrays["adapted"].view("<u2") != arrays["upstream"].astype("<f2").view("<u2")))
            require(all(recorded[k] is True for k in ("inputs_unchanged", "allocation_guards_unchanged",
                    "upstream_final_denominators_positive", "upstream_final_maxima_finite")), "Runtime check did not pass")
        require(all(report[k] == 12 for k in ("trials", "adapted_launches", "upstream_forward_launches", "explicit_upstream_initialization_launches")), "Launch count differs")
        require(report["paired_output_values"] == count and report["cpu_reference_comparisons"] == 2 * count, "Aggregate count differs")
        for label in maxima:
            require(report[label + "_numerical_failures"] == 0 and report[label + "_max_abs_error"] == maxima[label], "Aggregate numerical result differs")
            hashes[label].append(hashlib.sha256(raw[label]).hexdigest())
        summaries.append({"device": report["device"], "trials": 12,
                          "paired_output_values": count, "cpu_reference_comparisons": 2 * count,
                          "max_abs_error": maxima, "adapted_vs_rounded_upstream_bit_differences": differences,
                          "compiler_input_files": len(headers), "report_sha256": sha(host / "results.json")})
    return {"schema": 1, "status": "native-fp16-online-attention-audited", "hosts": summaries,
            "fresh_cpu_reference_cases": 12, "paired_output_values": count * len(hosts),
            "cpu_reference_comparisons": 2 * count * len(hosts), "numerical_failures": 0,
            "max_abs_error": {k: max(h["max_abs_error"][k] for h in summaries) for k in maxima},
            "output_sha256": hashes, "cross_host_streams_identical": {k: len(set(v)) == 1 for k, v in hashes.items()},
            "native_source_sha256": meta["native_source_sha256"], "input_manifest_sha256": sha(data / "manifest.json"),
            "source_certificates": 0, "whole_kernel_execution_proved": False,
            "actual_trace_classification_proved": False, "ieee_equivalence_proved": False,
            "runtime_guard_and_upstream_final_accumulator_checks_reported": True,
            "accumulator_streams_independently_rechecked": False,
            "model_calls": 0, "original_paper_fully_reproduced": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--host", required=True, type=Path, action="append")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "Output exists")
    report = check(args.input.resolve(), [p.resolve() for p in args.host])
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "hosts"}))


if __name__ == "__main__":
    main()
