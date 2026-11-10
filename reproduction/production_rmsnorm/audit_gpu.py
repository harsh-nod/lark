"""Recompute native RMSNorm measurements from frozen binary streams (stdlib only)."""

import argparse
from array import array
import hashlib
import json
import math
from pathlib import Path
import struct
import sys
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest(root, files):
    for name, digest in files.items():
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or sha(root / path) != digest:
            raise ValueError("Manifest member differs: " + name)


def half_words(path):
    words = array("H")
    words.frombytes(path.read_bytes())
    if sys.byteorder != "little":
        words.byteswap()
    return words


def audit(data, result):
    verify_manifest(data, json.loads((data / "manifest.json").read_text())["files"])
    verify_manifest(result, json.loads((result / "manifest.json").read_text()))
    metadata = json.loads((data / "dataset.json").read_text())
    report = json.loads((result / "results.json").read_text())
    assert report["input_manifest_sha256"] == sha(data / "manifest.json")
    assert report["adapted_sha256"] == sha(result / "adapted.bin")
    assert report["upstream_sha256"] == sha(result / "upstream.bin")
    assert report["binary_sha256"] == sha(result / "driver.so")
    assert report["status"] == "passed" and report["numerical_failures"] == 0
    assert report["complete_source_proof"] is False and report["certificates"] == 0
    assert report["original_paper_fully_reproduced"] is False and report["model_calls"] == 0
    guard = json.loads((result / "memory-guard.json").read_text())
    assert guard["minimum_free_fraction"] == 0.98
    assert guard["free_bytes"] >= guard["total_bytes"] * 0.98
    compiler_inputs = json.loads((result / "compiler-inputs.json").read_text())
    with tarfile.open(result / "compiler-inputs.tar.gz") as archive:
        members = archive.getmembers()
        assert len(members) == len(compiler_inputs) == report["compiler_inputs"]
        assert len({m.name for m in members}) == len(members)
        for member in members:
            assert member.isfile() and ".." not in Path(member.name).parts
            expected_hash = compiler_inputs["/" + member.name]
            assert hashlib.sha256(archive.extractfile(member).read()).hexdigest() == expected_hash
    a, b, e, tree = [
        half_words(path)
        for path in (
            result / "adapted.bin",
            result / "upstream.bin",
            data / "expected.bin",
            data / "source-tree.bin",
        )
    ]
    total = sum(c["elements"] * len(c["trials"]) for c in metadata["cases"])
    assert len(a) == len(b) == len(e) == len(tree) == total
    assert (data / "input.bin").stat().st_size == total * 2
    assert (data / "weight.bin").stat().st_size == 24 * 16384 * 2
    floats = [struct.unpack("<e", i.to_bytes(2, "little"))[0] for i in range(65536)]
    bitdiff = signedzero = nonzero = max_ulp = source_bits = upstream_torch_bits = (
        adapted_torch_bits
    ) = 0
    cases = []
    for case, measured in zip(metadata["cases"], report["cases"], strict=True):
        assert case["rows"] == measured["rows"] == case["grid"] == measured["grid"]
        assert case["block"] == measured["block"] == 1024
        assert case["warp"] == measured["warp"] == 64
        trials = []
        for trial, claimed in zip(case["trials"], measured["trials"], strict=True):
            assert trial.items() <= claimed.items()
            start, count = trial["offset_bytes"] // 2, case["elements"]
            bits = zeros = different = ulp = tree_bits = up_bits = ad_bits = 0
            errors = [0.0, 0.0]
            for i in range(start, start + count):
                x, y, exp, t = a[i], b[i], e[i], tree[i]
                assert exp & 0x7C00 != 0x7C00
                if x != y:
                    bits += 1
                    if (x & 32767) == (y & 32767) == 0:
                        zeros += 1
                    else:
                        different += 1
                        assert (x & 32768) == (y & 32768)
                        ulp = max(ulp, abs((x & 32767) - (y & 32767)))
                tree_bits += x != t
                up_bits += y != exp
                ad_bits += x != exp
                for method, word in enumerate((x, y)):
                    assert word & 0x7C00 != 0x7C00
                    if word != exp:
                        error = abs(floats[word] - floats[exp])
                        assert math.isfinite(error)
                        assert error <= metadata["atol"] + metadata["rtol"] * abs(floats[exp]), (
                            "Numerical tolerance violated in raw stream"
                        )
                        errors[method] = max(errors[method], error)
            assert claimed["bit_differences"] == bits
            assert claimed["source_tree_cpu_bit_differences"] == tree_bits
            assert claimed["paired_output_values"] == count
            assert claimed["cpu_reference_comparisons"] == count * 2
            for method, label in enumerate(("adapted", "upstream")):
                assert claimed[label + "_max_abs_error"] == errors[method]
                assert claimed[label + "_numerical_failures"] == 0
            assert (
                claimed["inputs_unchanged"]
                and claimed["weights_unchanged"]
                and claimed["all_allocation_guards_unchanged"]
            )
            trials.append(
                {
                    "trial": trial["trial"],
                    "bit_differences": bits,
                    "signed_zero_differences": zeros,
                    "nonzero_differences": different,
                    "max_nonzero_half_ulp": ulp,
                    "adapted_max_abs_error": errors[0],
                    "upstream_max_abs_error": errors[1],
                }
            )
            bitdiff += bits
            signedzero += zeros
            nonzero += different
            max_ulp = max(max_ulp, ulp)
            source_bits += tree_bits
            upstream_torch_bits += up_bits
            adapted_torch_bits += ad_bits
        cases.append({"rows": case["rows"], "trials": trials})
        print(json.dumps({"audited_rows": case["rows"], "trials": len(trials)}), flush=True)
    assert (
        report["paired_output_values"] == total and report["cpu_reference_comparisons"] == 2 * total
    )
    assert (
        report["bit_differences"] == bitdiff
        and report["source_tree_cpu_bit_differences"] == source_bits
    )
    assert report["trials"] == 24 and report["launches"] == 48
    assert report["max_abs_error"] == max(
        t[label + "_max_abs_error"]
        for c in cases
        for t in c["trials"]
        for label in ("adapted", "upstream")
    )
    return {
        "status": "passed",
        "paired_output_values": total,
        "cpu_reference_comparisons": total * 2,
        "bit_differences": bitdiff,
        "signed_zero_differences": signedzero,
        "nonzero_differences": nonzero,
        "max_nonzero_half_ulp": max_ulp,
        "adapted_torch_bit_differences": adapted_torch_bits,
        "upstream_torch_bit_differences": upstream_torch_bits,
        "cases": cases,
        "complete_source_proof": False,
        "certificates": 0,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, type=Path)
    p.add_argument("--results", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    report = audit(args.input.resolve(), args.results.resolve())
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "cases"}), flush=True)


if __name__ == "__main__":
    main()
