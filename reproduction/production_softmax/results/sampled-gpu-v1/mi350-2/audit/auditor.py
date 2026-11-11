"""Independently audit both full native softmax output streams against CPU data."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def manifest(directory, nested=False):
    value = json.loads((directory / "manifest.json").read_text())
    records = value["files"] if nested else value
    for name, expected in records.items():
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or sha(directory / path) != expected:
            raise ValueError("Artifact path/hash mismatch: " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--device-output", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, device, out = args.input.resolve(), args.device_output.resolve(), args.output.resolve()
    manifest(data, True)
    manifest(device)
    metadata = json.loads((data / "dataset.json").read_text())
    runtime = json.loads((device / "results.json").read_text())
    if (runtime["status"] != "runtime-checks-passed-pending-independent-numerical-audit"
            or runtime["input_manifest_sha256"] != sha(data / "manifest.json")
            or runtime["trials"] != 24 or runtime["launches"] != 48
            or runtime["runner_sha256"] != sha(data / "run_gpu.py")
            or not all(r["all_allocation_guards_unchanged"] and r["input_unchanged"] for r in runtime["cases"])):
        raise ValueError("Unexpected runtime record")
    import numpy as np

    total = sum(c["elements"] * len(c["trials"]) for c in metadata["cases"])
    streams = {name: np.memmap(path, dtype="<f2", mode="r") for name, path in {
        "reference": data / "expected.bin", "racy-output": device / "racy-output.bin",
        "fixed-output": device / "fixed-output.bin",
    }.items()}
    if any(values.size != total for values in streams.values()):
        raise ValueError("Output/reference element count differs")
    methods = {name: {"comparisons": 0, "failed": 0, "nonfinite": 0, "max_abs_error": 0., "max_rel_error": 0.}
               for name in ("racy-output", "fixed-output")}
    records, paired_bit_differences = [], 0
    for case in metadata["cases"]:
        n = case["elements"]
        for trial in case["trials"]:
            offset = trial["offset_elements"]
            ref = streams["reference"][offset:offset+n]
            if hashlib.sha256(ref.tobytes()).hexdigest() != trial["expected_sha256"]:
                raise ValueError("Trial reference hash differs")
            item = {"rows": case["rows"], "trial": trial["trial"], "family": trial["family"],
                    "elements": n, "methods": {}, "paired_bit_differences": 0}
            for start in range(0, n, 131072):
                stop = min(n, start + 131072)
                expected = ref[start:stop].astype(np.float64)
                for name, counts in methods.items():
                    actual = streams[name][offset+start:offset+stop].astype(np.float64)
                    finite = np.isfinite(actual)
                    absolute = np.abs(actual - expected)
                    failures = ~finite | (absolute > metadata["atol"] + metadata["rtol"] * np.abs(expected))
                    relative = np.divide(absolute, np.abs(expected), out=np.zeros_like(absolute), where=expected != 0)
                    found = int(failures.sum())
                    counts["comparisons"] += stop - start
                    counts["failed"] += found
                    counts["nonfinite"] += int((~finite).sum())
                    counts["max_abs_error"] = max(counts["max_abs_error"], float(np.max(absolute)))
                    counts["max_rel_error"] = max(counts["max_rel_error"], float(np.max(relative)))
                    item["methods"].setdefault(name, {"comparisons": 0, "failed": 0})
                    item["methods"][name]["comparisons"] += stop - start
                    item["methods"][name]["failed"] += found
                a = streams["racy-output"][offset+start:offset+stop].view("<u2")
                b = streams["fixed-output"][offset+start:offset+stop].view("<u2")
                item["paired_bit_differences"] += int((a != b).sum())
            paired_bit_differences += item["paired_bit_differences"]
            records.append(item)
    passed = all(v["failed"] == 0 and v["nonfinite"] == 0 and v["comparisons"] == total for v in methods.values())
    out.mkdir(parents=True, exist_ok=False)
    report = {
        "schema": 1, "status": "full-native-softmax-numerical-checks-passed" if passed else "numerical-mismatch",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "device": runtime["device"],
        "numpy": np.__version__, "trials": 24, "launches": 48,
        "atol": metadata["atol"], "rtol": metadata["rtol"], "reference": metadata["reference"],
        "methods": methods, "paired_bit_differences": paired_bit_differences,
        "methods_bit_identical_on_sample": paired_bit_differences == 0,
        "source_sha256": {name: sha(data / name / "kernel.hip") for name in ("native_race", "native_fixed")},
        "input_manifest_sha256": sha(data / "manifest.json"), "device_manifest_sha256": sha(device / "manifest.json"),
        "compiler_input_hashes_sha256": sha(device / "compiler-inputs.json"),
        "whole_kernel_lean_execution_proved": False, "source_certificates": 0,
        "original_source_race_free": False, "repair_universal_race_freedom_proved": False,
        "ieee_equivalence_proved": False, "floating_point_error_bound_proved": False,
        "original_paper_fully_reproduced": False, "model_calls": 0, "records": records,
        "scope": "Finite paired AMD numerical trials of independent full three-pass FP16 sources. Each method is compared independently with CPU-float64 stable softmax rounded to FP16 at the end. The original clamped-load source has a source-level race; agreement on this finite sample does not establish race freedom or a universal equality theorem. Historical models, original adapted text and NVIDIA timings are not reproduced.",
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "auditor.py")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "comparisons_per_method": total,
                      "failed": sum(v["failed"] for v in methods.values()), "paired_bit_differences": paired_bit_differences}))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
