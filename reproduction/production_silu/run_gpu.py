"""Run exact certified multiwave kernels and the extracted upstream scalar path."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import struct
import subprocess


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest = json.loads((data / "manifest.json").read_text())
    for name, digest in manifest["files"].items():
        if sha(data / name) != digest:
            raise ValueError("Input differs: " + name)
    out.mkdir(parents=True, exist_ok=False)
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-shared",
        "-fPIC",
        "-ffp-contract=off",
        "-DUSE_ROCM",
        "-I" + str(data / "torch_headers"),
        "--offload-arch=gfx950",
        str(data / "driver.hip"),
        "-o",
        str(out / "driver.so"),
    ]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    hip = C.CDLL("/opt/rocm/lib/libamdhip64.so")
    hip.hipGetErrorString.argtypes = [C.c_int]
    hip.hipGetErrorString.restype = C.c_char_p
    hip.hipMemGetInfo.argtypes = [C.POINTER(C.c_size_t), C.POINTER(C.c_size_t)]
    hip.hipMalloc.argtypes = [C.POINTER(C.c_void_p), C.c_size_t]
    hip.hipMemcpy.argtypes = [C.c_void_p, C.c_void_p, C.c_size_t, C.c_int]
    hip.hipFree.argtypes = [C.c_void_p]
    hip.hipDeviceGetName.argtypes = [C.c_char_p, C.c_int, C.c_int]

    def checked(code):
        if code:
            raise RuntimeError(hip.hipGetErrorString(code).decode())

    checked(hip.hipSetDevice(0))
    free, total = C.c_size_t(), C.c_size_t()
    checked(hip.hipMemGetInfo(C.byref(free), C.byref(total)))
    memory_guard = {
        "free_bytes": free.value,
        "total_bytes": total.value,
        "minimum_free_fraction": 0.98,
    }
    (out / "memory-guard.json").write_text(json.dumps(memory_guard, indent=2) + "\n")
    if free.value < total.value * 0.98:
        raise RuntimeError("Selected GPU memory is occupied; no trials executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_case.argtypes = [C.c_int, C.c_void_p, C.c_void_p, C.c_void_p]
    lib.run_case.restype = C.c_int
    lib.runtime_attribute.argtypes = [C.c_int]
    lib.runtime_attribute.restype = C.c_int
    warp, max_threads = lib.runtime_attribute(0), lib.runtime_attribute(1)
    metadata = json.loads((data / "dataset.json").read_text())
    if warp != 64 or any(c["warp"] != warp or c["block"] > max_threads for c in metadata["cases"]):
        raise ValueError("Native wave/launch contract differs")
    device_name = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device_name, len(device_name), 0))
    input_bytes, expected_bytes = (
        (data / "input.bin").read_bytes(),
        (data / "expected.bin").read_bytes(),
    )
    guard = b"\x5a" * 128
    cases = []
    adapted_all, upstream_all = bytearray(), bytearray()
    for case in metadata["cases"]:
        n_input, n_output = case["input_elements"], case["output_elements"]
        result = {
            "key": case["key"],
            "grid": case["grid"],
            "block": case["block"],
            "warp": warp,
            "trials": [],
            "bit_differences": 0,
            "numerical_failures": 0,
            "cpu_reference_comparisons": 0,
            "max_abs_error": 0.0,
        }
        for trial in range(case["trials"]):
            ioff = case["input_offset_bytes"] + trial * n_input * 2
            ooff = case["output_offset_bytes"] + trial * n_output * 2
            inputs = input_bytes[ioff : ioff + n_input * 2]
            expected = struct.unpack(
                "<" + str(n_output) + "e", expected_bytes[ooff : ooff + n_output * 2]
            )
            payloads = [b"\x00\x7e" * n_output, inputs, b"\x00\x7e" * n_output]
            pointers = []
            try:
                for payload in payloads:
                    ptr = C.c_void_p()
                    checked(hip.hipMalloc(C.byref(ptr), len(payload) + 256))
                    pointers.append(ptr)
                    host = C.create_string_buffer(guard + payload + guard)
                    checked(hip.hipMemcpy(ptr, host, len(payload) + 256, 1))
                checked(lib.run_case(case["id"], *(C.c_void_p(p.value + 128) for p in pointers)))
                checked(hip.hipDeviceSynchronize())
                raw = []
                for index, (ptr, payload) in enumerate(zip(pointers, payloads)):
                    host = C.create_string_buffer(len(payload) + 256)
                    checked(hip.hipMemcpy(host, ptr, len(payload) + 256, 2))
                    actual = host.raw
                    if actual[:128] != guard or actual[-128:] != guard:
                        raise RuntimeError("Allocation guard modified")
                    actual = actual[128:-128]
                    if index == 1 and actual != payload:
                        raise RuntimeError("Input bytes modified")
                    raw.append(actual)
                adapted_all.extend(raw[0])
                upstream_all.extend(raw[2])
                bit_differences = (
                    0
                    if raw[0] == raw[2]
                    else sum(
                        raw[0][i : i + 2] != raw[2][i : i + 2] for i in range(0, n_output * 2, 2)
                    )
                )
                max_error, failures = 0.0, 0
                for actual in (raw[0], raw[2]):
                    for got, exp in zip(struct.unpack("<" + str(n_output) + "e", actual), expected):
                        error = abs(got - exp)
                        max_error = max(max_error, error)
                        if not math.isfinite(got) or error > metadata["atol"] + metadata[
                            "rtol"
                        ] * abs(exp):
                            failures += 1
                result["bit_differences"] += bit_differences
                result["numerical_failures"] += failures
                result["cpu_reference_comparisons"] += 2 * n_output
                result["max_abs_error"] = max(result["max_abs_error"], max_error)
                result["trials"].append(
                    {
                        "trial": trial,
                        "paired_output_values": n_output,
                        "cpu_reference_comparisons": 2 * n_output,
                        "bit_differences": bit_differences,
                        "numerical_failures": failures,
                        "max_abs_error": max_error,
                        "inputs_unchanged": True,
                        "all_allocation_guards_unchanged": True,
                    }
                )
            finally:
                for ptr in pointers:
                    checked(hip.hipFree(ptr))
        cases.append(result)
    (out / "adapted.bin").write_bytes(adapted_all)
    (out / "upstream.bin").write_bytes(upstream_all)
    differences = sum(c["bit_differences"] for c in cases)
    failures = sum(c["numerical_failures"] for c in cases)
    report = {
        "status": "passed" if not differences and not failures else "failed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "device": device_name.value.decode(),
        "architecture": "gfx950",
        "warp": warp,
        "max_threads_per_block": max_threads,
        "cases": cases,
        "trials": sum(len(c["trials"]) for c in cases),
        "launches_per_trial": 2,
        "paired_output_values": len(adapted_all) // 2,
        "cpu_reference_comparisons": sum(c["cpu_reference_comparisons"] for c in cases),
        "bit_differences": differences,
        "numerical_failures": failures,
        "max_abs_error": max(c["max_abs_error"] for c in cases),
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "adapted_sha256": sha(out / "adapted.bin"),
        "upstream_sha256": sha(out / "upstream.bin"),
        "binary_sha256": sha(out / "driver.so"),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": metadata["scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: report[k]
                for k in (
                    "status",
                    "device",
                    "trials",
                    "paired_output_values",
                    "cpu_reference_comparisons",
                    "bit_differences",
                    "numerical_failures",
                    "max_abs_error",
                )
            }
        )
    )
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
