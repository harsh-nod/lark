"""Fresh CPU float64/Torch audits of every native in-place Q/K output."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rope as native


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root, hashes):
    for name, expected in hashes.items():
        path = (root / name).resolve()
        if not path.is_relative_to(root.resolve()) or sha(path) != expected:
            raise ValueError("File binding differs: " + name)


def require_scope(report):
    if (type(report["source_certificates"]) is not int or report["source_certificates"] != 0
            or report["whole_kernel_execution_proved"] is not False
            or report["original_paper_fully_reproduced"] is not False
            or type(report["model_calls"]) is not int or report["model_calls"] != 0):
        raise ValueError("Unsupported numerical-evidence scope claim")


def audit(data, host_paths):
    import numpy as np
    import torch
    torch.set_num_threads(1)
    verify(data, json.loads((data / "manifest.json").read_text())["files"])
    metadata = json.loads((data / "dataset.json").read_text())
    require_scope(metadata)
    if (metadata["layouts"] != list(native.LAYOUTS)
            or metadata["atol"] != .002 or metadata["rtol"] != .002
            or [(r["rows"], r["trial"]) for r in metadata["cases"]] != [
                (rows, trial) for rows in (1, 3, 64, 256) for trial in
                ("normal", "signed-zero", "structured", "cancellation", "wide", "small")]):
        raise ValueError("Numerical cohort/tolerance differs")
    expected_records = [(c["rows"], c["trial"], layout) for c in metadata["cases"] for layout in native.LAYOUTS]
    total_rows = sum(c["rows"] for c in metadata["cases"])
    reference_functions = {}
    for layout in native.LAYOUTS:
        source = (data / layout / "reference.py").read_text()
        native.check_reference(source, layout)
        namespace = {}
        exec(compile(source, "checked-native-rope-reference", "exec"), namespace)
        reference_functions[layout] = namespace["reference"]
    inputs = {name: np.memmap(data / (name + ".bin"), dtype="<f2", mode="r")
              for name in ("query", "key", "cache")}
    names = [f"{layout}-{method}-{name}" for layout in native.LAYOUTS
             for method in ("adapted", "upstream") for name in ("query", "key")]
    hosts, streams = [], []
    for root in host_paths:
        verify(root, json.loads((root / "manifest.json").read_text()))
        report = json.loads((root / "results.json").read_text())
        require_scope(report)
        if (report["input_manifest_sha256"] != sha(data / "manifest.json")
                or report["runner_sha256"] != sha(data / "run_gpu.py")
                or report["trials"] != 48 or report["launches"] != 96
                or report["output_elements_per_method"] != total_rows * 5120 * 2
                or report["block"] != 512 or report["warp"] != 64
                or report["actual_trace_classification_proved"] is not False
                or report["original_nvidia_kernel_executed"] is not False
                or report["upstream_device_bodies_retained"] is not True
                or report["VLLM_LDG_replaced_with_plain_hip_load"] is not True):
            raise ValueError("Runtime binding or scope differs")
        if [(r["rows"], r["trial"], r["layout"]) for r in report["cases"]] != expected_records:
            raise ValueError("Runtime trial record differs")
        if any(not all(r[k] is True for k in ("all_allocation_guards_unchanged", "cache_unchanged", "positions_unchanged"))
               or r["query_elements"] != r["rows"] * 4096 or r["key_elements"] != r["rows"] * 1024
               for r in report["cases"]):
            raise ValueError("Runtime guard record differs")
        for name in names:
            width = 4096 if name.endswith("-query") else 1024
            path = root / (name + ".bin")
            if path.stat().st_size != total_rows * width * 2 or sha(path) != report["output_sha256"][name]:
                raise ValueError("Truncated, enlarged or rebound output stream")
        streams.append({name: np.memmap(root / (name + ".bin"), dtype="<f2", mode="r") for name in names})
        hosts.append({"directory": root.name, "device": report["device"], "trials": 48,
                      "compiler_inputs": report["compiler_inputs"], "runtime_report_sha256": sha(root / "results.json"),
                      "comparisons": 0, "tolerance_failures": 0, "max_abs_error": 0.,
                      "torch_fp32_bit_differences": 0, "torch_signed_zero_differences": 0,
                      "adapted_vs_upstream_bit_differences": 0, "details": []})
    offset_rows = 0
    for case in metadata["cases"]:
        rows = case["rows"]
        arrays = {}
        for name, heads in (("query", 32), ("key", 8), ("cache", 1)):
            start = case["offset_bytes"][name] // 2
            size = rows * heads * 128
            array = inputs[name][start:start + size]
            if len(array) != size or hashlib.sha256(array.tobytes()).hexdigest() != case["sha256"][name]:
                raise ValueError("Case operand binding differs")
            arrays[name] = np.array(array).reshape(rows, heads, 128)
            if not np.isfinite(array).all():
                raise ValueError("Nonfinite prepared operand")
        for layout in native.LAYOUTS:
            torch_values = reference_functions[layout](
                torch.from_numpy(arrays["query"]), torch.from_numpy(arrays["key"]),
                torch.from_numpy(arrays["cache"][:, 0, :]))
            c = arrays["cache"][:, :, :64].astype(np.float64)
            s = arrays["cache"][:, :, 64:].astype(np.float64)
            for bi, (name, width) in enumerate((("query", 4096), ("key", 1024))):
                source = arrays[name].astype(np.float64)
                if layout == "split-half":
                    x, y = source[..., :64], source[..., 64:]
                    ref64 = np.concatenate((x * c - y * s, y * c + x * s), axis=-1).reshape(-1)
                else:
                    x, y = source[..., 0::2], source[..., 1::2]
                    ref64 = np.stack((x * c - y * s, y * c + x * s), axis=-1).reshape(-1)
                ref_bits = torch_values[bi].numpy().reshape(-1).view("<u2")
                sl = slice(offset_rows * width, (offset_rows + rows) * width)
                for host, values in zip(hosts, streams):
                    for method in ("adapted", "upstream"):
                        got = values[f"{layout}-{method}-{name}"][sl]
                        errors = np.abs(got.astype(np.float64) - ref64)
                        failures = int(np.count_nonzero(~np.isfinite(got) | (errors > .002 + .002 * np.abs(ref64))))
                        bits = got.view("<u2")
                        different = bits != ref_bits
                        zeros = different & ((bits & 0x7fff) == 0) & ((ref_bits & 0x7fff) == 0)
                        host["comparisons"] += got.size
                        host["tolerance_failures"] += failures
                        host["max_abs_error"] = max(host["max_abs_error"], float(errors.max()))
                        host["torch_fp32_bit_differences"] += int(np.count_nonzero(different))
                        host["torch_signed_zero_differences"] += int(np.count_nonzero(zeros))
                        host["details"].append({"rows": rows, "trial": case["trial"], "layout": layout,
                                                "buffer": name, "method": method, "comparisons": int(got.size),
                                                "tolerance_failures": failures,
                                                "torch_fp32_bit_differences": int(np.count_nonzero(different))})
                    host["adapted_vs_upstream_bit_differences"] += int(np.count_nonzero(
                        values[f"{layout}-adapted-{name}"][sl].view("<u2") !=
                        values[f"{layout}-upstream-{name}"][sl].view("<u2")))
        offset_rows += rows
    hashes = {name: [sha(root / (name + ".bin")) for root in host_paths] for name in names}
    failures = sum(h["tolerance_failures"] for h in hosts)
    return {"schema": 1, "status": "passed" if not failures else "failed", "hosts": hosts,
            "fresh_cpu_float64_reference_cases": len(metadata["cases"]) * 2,
            "fresh_cpu_torch_reference_cases": len(metadata["cases"]) * 2,
            "torch_version": torch.__version__, "numpy_version": np.__version__,
            "comparisons": sum(h["comparisons"] for h in hosts), "tolerance_failures": failures,
            "torch_fp32_bit_differences": sum(h["torch_fp32_bit_differences"] for h in hosts),
            "adapted_vs_upstream_bit_differences": sum(h["adapted_vs_upstream_bit_differences"] for h in hosts),
            "cross_host_streams_identical": {name: len(set(values)) == 1 for name, values in hashes.items()},
            "output_sha256": hashes, "input_manifest_sha256": sha(data / "manifest.json"),
            "auditor_sha256": sha(Path(__file__)), "whole_kernel_execution_proved": False,
            "source_certificates": 0, "model_calls": 0, "original_paper_fully_reproduced": False,
            "scope": "Finite independent HIP adaptation and retained-upstream HIP comparison on AMD. Float64 tolerance and Torch FP32 bit comparisons are separate; no universal source/reference, IEEE or original NVIDIA result is claimed."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("Fresh audit output required")
    result = audit(args.input.resolve(), [p.resolve() for p in args.host])
    args.output.mkdir(parents=True)
    (args.output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "manifest.json").write_text(json.dumps({"results.json": sha(args.output / "results.json")}, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "comparisons", "tolerance_failures",
                                            "torch_fp32_bit_differences", "adapted_vs_upstream_bit_differences")}))
    if result["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
