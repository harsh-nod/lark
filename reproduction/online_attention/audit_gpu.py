"""Independently recompute every numerical comparison from frozen Q/K/V streams.

This checks finite numerical evidence. It is not a GPU race detector or a proof
that the source implements the exact-real value recurrence.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def manifest(root):
    files = json.loads((root / "manifest.json").read_text())
    require(all(Path(n).name == n and n != "manifest.json" for n in files), "Nonlocal manifest path")
    require({p.name for p in root.iterdir() if p.is_file()} == set(files) | {"manifest.json"}, "File inventory differs")
    require(all(sha(root / n) == h for n, h in files.items()), "Manifest hash differs")


def check(input_root, hosts):
    import numpy as np
    import torch

    torch.set_num_threads(1)
    manifest(input_root)
    meta = json.loads((input_root / "dataset.json").read_text())
    source = (input_root / "flash.cu").read_text()
    body = source[source.index("__global__"):source.index("\ntorch::Tensor forward(")]
    require(body.encode() == (input_root / "upstream_context.cuh").read_bytes(), "Kernel extraction differs")
    require(hashlib.sha256(body.encode()).hexdigest() == meta["upstream_definition_sha256"], "Kernel definition hash differs")
    require(meta["kernel_definition_unchanged"] is True and meta["tile"] == 32, "Changed source scope")
    require(meta["source_certificates"] == 0 and meta["model_calls"] == 0, "Unsupported certificate/model count")
    flags = ("whole_kernel_execution_proved", "race_freedom_proved", "ieee_equivalence_proved", "original_paper_fully_reproduced")
    require(all(meta[k] is False for k in flags), "Unsupported formal or original-paper claim")
    require(meta["atol"] == 0.0001 and meta["rtol"] == 0.0002, "Comparison tolerance differs")
    streams = {k: (input_root / (k + ".bin")).read_bytes() for k in ("q", "k", "v", "expected")}
    cases = meta["cases"]
    expected_shapes = {(1, 1, 32, 32), (1, 1, 64, 64), (1, 1, 128, 256), (2, 3, 64, 64)}
    expected_families = {"seeded-normal", "zero-scores", "constant-scores", "alternating", "sharp", "large-common-score-shift"}
    require(len(cases) == 24 and {(c["batch"], c["heads"], c["n"], c["d"]) for c in cases} == expected_shapes, "Case coverage differs")
    require(len({(c["batch"], c["heads"], c["n"], c["d"], c["family"]) for c in cases}) == 24
            and {c["family"] for c in cases} == expected_families, "Case family coverage differs")
    reference = []
    count = 0
    for case in cases:
        dims = tuple(case[k] for k in ("batch", "heads", "n", "d"))
        size = math.prod(dims)
        require(case["elements"] == size and case["offset_elements"] == count, "Case extent differs")
        q, k, v = [torch.from_numpy(np.frombuffer(streams[key], dtype="<f4", count=size, offset=count * 4).copy().reshape(dims)).double() for key in ("q", "k", "v")]
        require(all(torch.equal(x, x.half().double()) for x in (q, k, v)), "Input is not half-representable")
        score = (q @ k.transpose(-1, -2)) / math.sqrt(case["d"])
        require(float(score.min()) == case["reference_score_min"] and float(score.max()) == case["reference_score_max"], "Reference score range differs")
        values = (score.softmax(dim=-1) @ v).numpy().astype("<f8").tobytes()
        require(values == streams["expected"][count * 8:(count + size) * 8], "Fresh CPU reference differs")
        reference.append(np.frombuffer(values, dtype="<f8"))
        count += size
    require(all(len(v) == count * (8 if k == "expected" else 4) for k, v in streams.items()), "Input stream extent differs")
    summaries = []
    output_hashes = []
    for root in hosts:
        manifest(root)
        report = json.loads((root / "results.json").read_text())
        require(report["input_manifest_sha256"] == sha(input_root / "manifest.json"), "Input binding differs")
        require(all(report[k] is False for k in flags), "Unsupported formal or original-paper claim")
        require(report["source_certificates"] == 0 and report["model_calls"] == 0, "Unsupported certificate/model count")
        require(report["atol"] == meta["atol"] and report["rtol"] == meta["rtol"], "Reported tolerance differs")
        require(report["warp"] == 64 and report["shared_per_block"] >= 102400, "Native launch capacity differs")
        guard = json.loads((root / "memory-guard.json").read_text())
        require(guard["minimum_free_fraction"] == 0.98 and guard["free_bytes"] >= 0.98 * guard["total_bytes"], "Memory guard did not pass")
        header_manifest = json.loads((root / "compiler-inputs.json").read_text())
        with tarfile.open(root / "compiler-inputs.tar.gz") as archive:
            members = archive.getmembers()
            require(all(m.isfile() for m in members), "Compiler capture has a nonfile member")
            require(len(members) == len(header_manifest) and {m.name for m in members} == {n.lstrip("/") for n in header_manifest}, "Compiler capture inventory differs")
            for member in members:
                content = archive.extractfile(member).read()
                require(hashlib.sha256(content).hexdigest() == header_manifest["/" + member.name], "Compiler input differs")
            for filename in ("driver.hip", "upstream_context.cuh"):
                matches = [m for m in members if m.name.endswith("/" + filename)]
                require(len(matches) == 1 and archive.extractfile(matches[0]).read() == (input_root / filename).read_bytes(), "Compiled source differs: " + filename)
        require(report["compiler_input_files"] == len(header_manifest), "Compiler input count differs")
        raw = (root / "outputs.bin").read_bytes()
        require(len(raw) == count * 4 and len(report["cases"]) == len(cases), "Output extent differs")
        maximum = 0.0
        for case, recorded, expected in zip(cases, report["cases"], reference):
            require(all(recorded[k] == v for k, v in case.items()), "Recorded case differs")
            actual = np.frombuffer(raw, dtype="<f4", count=case["elements"], offset=case["offset_elements"] * 4).astype(np.float64)
            error = np.abs(actual - expected)
            failures = int(np.count_nonzero(~np.isfinite(actual) | ~np.isfinite(expected) | (error > meta["atol"] + meta["rtol"] * np.abs(expected))))
            require(failures == 0 and recorded["numerical_failures"] == 0, "Numerical tolerance failure")
            require(recorded["output_comparisons"] == case["elements"] and recorded["max_abs_error"] == float(error.max()), "Recorded comparison differs")
            require(all(recorded[k] is True for k in ("inputs_unchanged", "allocation_guards_unchanged", "all_denominators_positive", "all_accumulator_maxima_finite")), "Runtime check did not pass")
            maximum = max(maximum, float(error.max()))
        require(report["trials"] == 24 and report["forward_kernel_launches"] == 24 and report["initialization_kernel_launches"] == 24, "Launch count differs")
        require(report["output_comparisons"] == count and report["numerical_failures"] == 0 and report["max_abs_error"] == maximum, "Aggregate differs")
        summaries.append({"device": report["device"], "trials": 24, "forward_kernel_launches": 24,
                          "initialization_kernel_launches": 24, "output_comparisons": count,
                          "numerical_failures": 0, "max_abs_error": maximum,
                          "compiler_input_files": len(header_manifest), "results_sha256": sha(root / "results.json")})
        output_hashes.append(hashlib.sha256(raw).hexdigest())
    return {
        "schema": 1, "status": "native-online-attention-audited", "hosts": summaries,
        "fresh_cpu_reference_cases": len(cases), "output_comparisons": count * len(hosts),
        "numerical_failures": 0, "max_abs_error": max(s["max_abs_error"] for s in summaries),
        "host_output_sha256": output_hashes, "host_outputs_byte_identical": len(set(output_hashes)) == 1,
        "upstream_definition_sha256": meta["upstream_definition_sha256"],
        "input_manifest_sha256": sha(input_root / "manifest.json"),
        "atol": meta["atol"], "rtol": meta["rtol"],
        "runtime_guard_and_accumulator_checks_reported": True,
        "accumulator_streams_independently_rechecked": False,
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "race_freedom_proved": False, "ieee_equivalence_proved": False,
        "model_calls": 0, "original_paper_fully_reproduced": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--host", required=True, action="append", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "Output already exists")
    result = check(args.input.resolve(), [p.resolve() for p in args.host])
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "hosts"}))


if __name__ == "__main__":
    main()
