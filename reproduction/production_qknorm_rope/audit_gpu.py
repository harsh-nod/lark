"""Fresh CPU float64/Torch FP32 audit of both native fused Q/K implementations."""

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_qknorm_rope as native


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(part)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--host", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name, expected in json.loads((data / "manifest.json").read_text())["files"].items():
        if sha(data / name) != expected:
            raise ValueError("Frozen input differs: " + name)
    import numpy as np
    import torch
    torch.set_num_threads(1)
    metadata = json.loads((data / "dataset.json").read_text())
    if metadata["atol"] != .002 or metadata["rtol"] != .002 or metadata["layouts"] != list(native.LAYOUTS):
        raise ValueError("Pinned numerical scope differs")
    wanted_inputs = [(rows, trial) for rows in (1, 3, 64, 256)
                     for trial in ("normal", "signed-zero", "structured", "cancellation", "wide", "small")]
    if [(c["rows"], c["trial"]) for c in metadata["cases"]] != wanted_inputs:
        raise ValueError("Pinned input cohort differs")
    references = {}
    for layout in native.LAYOUTS:
        text = (data / layout / "reference.py").read_text()
        native.check_reference(text, layout)
        namespace = {}
        exec(compile(text, "reference.py", "exec"), namespace)
        references[layout] = namespace["reference"]
    host_reports = []
    streams = []
    for directory in args.host:
        directory = directory.resolve()
        for name, expected in json.loads((directory / "manifest.json").read_text()).items():
            if Path(name).name != name or sha(directory / name) != expected:
                raise ValueError("Host artifact binding differs: " + name)
        report = json.loads((directory / "results.json").read_text())
        expected_cases = [(c["rows"], c["trial"], layout) for c in metadata["cases"] for layout in native.LAYOUTS]
        actual_cases = [(c["rows"], c["trial"], c["layout"]) for c in report["cases"]]
        if (report["status"] != "runtime-checks-passed-pending-independent-numerical-audit"
                or actual_cases != expected_cases or report["trials"] != 48 or report["launches"] != 96
                or report["input_manifest_sha256"] != sha(data / "manifest.json")
                or report["runner_sha256"] != sha(data / "run_gpu.py")
                or report["warp"] != 64 or report["block"] != 256 or report["logical_warp"] != 32
                or type(report["source_certificates"]) is not int or report["source_certificates"] != 0
                or any(report[k] is not False for k in ("whole_kernel_execution_proved", "dense_reference_equivalence_proved",
                                                       "actual_trace_classification_proved", "ieee_equivalence_proved"))
                or report["original_paper_fully_reproduced"] is not False
                or any(c[k] is not True for c in report["cases"] for k in
                       ("all_allocation_guards_unchanged", "all_readonly_inputs_unchanged", "upstream_v_heads_unchanged"))):
            raise ValueError("Host scope/trial/guard differs")
        outputs = {f"{layout}-{method}": (directory / f"{layout}-{method}.bin").open("rb")
                   for layout in native.LAYOUTS for method in ("adapted", "upstream")}
        for name, stream in outputs.items():
            if sha(directory / (name + ".bin")) != report["output_sha256"][name]:
                raise ValueError("Output binding differs")
        streams.append(outputs)
        host_reports.append({"host": directory.name, "runtime_manifest_sha256": sha(directory / "manifest.json"),
                             "records": [], "compared_values": 0, "tolerance_failures": 0,
                             "torch_fp32_bit_differences": 0, "adapted_upstream_bit_differences": 0})
    inputs = {n: (data / (n + ".bin")).open("rb") for n in ("qkv", "q_weight", "k_weight", "cache")}
    try:
        for case in metadata["cases"]:
            rows, payload = case["rows"], {}
            for name, count in (("qkv", rows * 6144), ("q_weight", 128), ("k_weight", 128), ("cache", rows * 128)):
                inputs[name].seek(case["offset_bytes"][name])
                raw = inputs[name].read(count * 2)
                if len(raw) != count * 2 or hashlib.sha256(raw).hexdigest() != case["sha256"][name]:
                    raise ValueError("CPU audit input differs")
                payload[name] = np.frombuffer(raw, dtype="<f2").copy()
            qkv = payload["qkv"].reshape(rows, 48, 128)
            cache = payload["cache"].reshape(rows, 128)
            x = qkv[:, :40, :].astype(np.float64)
            weights = np.concatenate((np.broadcast_to(payload["q_weight"], (32, 128)),
                                      np.broadcast_to(payload["k_weight"], (8, 128)))).astype(np.float64)
            normalized = x * ((1 / np.sqrt(np.mean(x * x, axis=-1, keepdims=True) + 1e-5)) * weights)
            c, s = cache[:, None, :64].astype(np.float64), cache[:, None, 64:].astype(np.float64)
            for layout in native.LAYOUTS:
                if layout == "interleaved":
                    a, b = normalized[..., ::2], normalized[..., 1::2]
                    expected64 = np.stack((a * c - b * s, a * s + b * c), axis=-1).reshape(rows, 40, 128)
                else:
                    a, b = normalized[..., :64], normalized[..., 64:]
                    expected64 = np.concatenate((a * c + (0.0 - b) * s, b * c + a * s), axis=-1)
                expected32 = references[layout](torch.from_numpy(qkv.copy()), torch.from_numpy(payload["q_weight"]),
                                                 torch.from_numpy(payload["k_weight"]), torch.from_numpy(cache)).numpy()
                expected64 = expected64.reshape(-1)
                expected32 = expected32.reshape(-1)
                for host, outputs in zip(host_reports, streams):
                    values = {}
                    for method in ("adapted", "upstream"):
                        raw = outputs[layout + "-" + method].read(rows * 10240)
                        if len(raw) != rows * 10240:
                            raise ValueError("Incomplete output stream")
                        actual = np.frombuffer(raw, dtype="<f2")
                        values[method] = actual
                        error = np.abs(actual.astype(np.float64) - expected64)
                        failures = int(np.count_nonzero(~np.isfinite(actual) | (error > .002 + .002 * np.abs(expected64))))
                        bits = int(np.count_nonzero(actual.view("<u2") != expected32.view("<u2")))
                        host["records"].append({"rows": rows, "trial": case["trial"], "layout": layout, "method": method,
                                                "compared_values": actual.size, "tolerance_failures": failures,
                                                "max_absolute_error_float64": float(error.max()), "torch_fp32_bit_differences": bits})
                        host["compared_values"] += actual.size
                        host["tolerance_failures"] += failures
                        host["torch_fp32_bit_differences"] += bits
                        if failures:
                            raise ValueError("Fresh CPU reference failed: " + str(host["records"][-1]))
                    host["adapted_upstream_bit_differences"] += int(np.count_nonzero(values["adapted"].view("<u2") != values["upstream"].view("<u2")))
        if any(stream.read(1) for outputs in streams for stream in outputs.values()):
            raise ValueError("Trailing unreported output data")
    finally:
        for stream in list(inputs.values()) + [s for outputs in streams for s in outputs.values()]:
            stream.close()
    report = {"schema": 1, "status": "native-fused-qknorm-rope-fresh-cpu-references-checked", "hosts": host_reports,
              "input_manifest_sha256": sha(data / "manifest.json"), "torch": torch.__version__, "numpy": np.__version__,
              "compared_values": sum(h["compared_values"] for h in host_reports), "atol": .002, "rtol": .002,
              "tolerance_failures": 0, "source_certificates": 0, "whole_kernel_execution_proved": False,
              "dense_reference_equivalence_proved": False, "ieee_equivalence_proved": False,
              "model_calls": 0, "new_gpu_trials": 0, "original_paper_fully_reproduced": False}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "manifest.json").write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "compared_values": report["compared_values"], "tolerance_failures": 0,
                      "torch_fp32_bit_differences": sum(h["torch_fp32_bit_differences"] for h in host_reports),
                      "adapted_upstream_bit_differences": sum(h["adapted_upstream_bit_differences"] for h in host_reports)}))


if __name__ == "__main__":
    main()
