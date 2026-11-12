"""Describe finite FP16 method differences; this does not accept a certificate."""

import argparse
import json
from pathlib import Path

from audit_gpu import sha, verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("Fresh rounding report required")
    data = args.input.resolve()
    verify(data, json.loads((data / "manifest.json").read_text())["files"])
    metadata = json.loads((data / "dataset.json").read_text())
    import numpy as np
    hosts = []
    for path in args.host:
        host = path.resolve()
        verify(host, json.loads((host / "manifest.json").read_text()))
        values = [np.memmap(host / (name + ".bin"), dtype="<f2", mode="r")
                  for name in ("adapted", "upstream")]
        if any(len(v) != metadata["outputs_per_method"] for v in values):
            raise ValueError("Truncated output stream")
        records = []
        for case in metadata["cases"]:
            for trial in case["trials"]:
                start = trial["offset_elements"]
                sl = slice(start, start + case["elements"])
                a, b = [v[sl] for v in values]
                if not np.isfinite(a).all() or not np.isfinite(b).all():
                    raise ValueError("Rounding analysis requires finite actual outputs")
                ab, bb = a.view("<u2"), b.view("<u2")
                different = ab != bb
                zero = different & ((ab & 32767) == 0) & ((bb & 32767) == 0)
                other = different & ~zero
                if np.any(different):
                    records.append({
                        "rows": case["rows"], "trial": trial["trial"], "label": trial["label"],
                        "bit_differences": int(different.sum()),
                        "signed_zero_differences": int(zero.sum()),
                        "other_bit_differences": int(other.sum()),
                        "nonzero_sign_disagreements": int(np.count_nonzero(
                            other & ((ab & 32767) != 0) & ((bb & 32767) != 0) & (((ab ^ bb) & 32768) != 0))),
                        "max_magnitude_ulp_difference": int(np.max(np.abs(
                            (ab[other] & 32767).astype(np.int32) - (bb[other] & 32767).astype(np.int32)))) if other.any() else 0,
                        "max_method_abs_difference": float(np.max(np.abs(a.astype(np.float64) - b.astype(np.float64)))),
                    })
        report = json.loads((host / "results.json").read_text())
        hosts.append({"directory": host.name, "hostname": report["hostname"], "records": records,
                      "bit_differences": sum(r["bit_differences"] for r in records),
                      "signed_zero_differences": sum(r["signed_zero_differences"] for r in records),
                      "other_bit_differences": sum(r["other_bit_differences"] for r in records),
                      "nonzero_sign_disagreements": sum(r["nonzero_sign_disagreements"] for r in records),
                      "max_magnitude_ulp_difference": max((r["max_magnitude_ulp_difference"] for r in records), default=0),
                      "max_method_abs_difference": max((r["max_method_abs_difference"] for r in records), default=0.),
                      "runtime_manifest_sha256": sha(host / "manifest.json")})
    result = {"schema": 1, "status": "finite-fp16-method-differences-described", "hosts": hosts,
              "input_manifest_sha256": sha(data / "manifest.json"), "analyzer_sha256": sha(Path(__file__)),
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "ieee_equivalence_proved": False, "new_gpu_trials": 0, "model_calls": 0,
              "original_paper_fully_reproduced": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "hosts": [
        {k: v for k, v in h.items() if k != "records"} for h in hosts]}), flush=True)


if __name__ == "__main__":
    main()
