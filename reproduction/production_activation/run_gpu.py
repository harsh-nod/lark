"""Compare the certified adaptation, extracted upstream scalar code and CPU data."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import struct
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest = json.loads((data / "manifest.json").read_text())
    for name, expected in manifest["files"].items():
        if sha(data / name) != expected:
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
    result = subprocess.run(command, capture_output=True, text=True, timeout=150)
    (out / "build.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(result.stderr)
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
    idle = {
        "free_bytes": free.value,
        "total_bytes": total.value,
        "requirement": "At least 98% GPU memory free immediately before trials",
    }
    (out / "memory-guard.json").write_text(json.dumps(idle, indent=2) + "\n")
    if free.value < total.value * 0.98:
        raise RuntimeError("GPU memory is occupied; refusing to execute trials")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_case.argtypes = [C.c_void_p, C.c_void_p, C.c_void_p]
    lib.run_case.restype = C.c_int
    device_name = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device_name, len(device_name), 0))
    dataset = json.loads((data / "dataset.json").read_text())
    guard = b"\x5a" * 128
    adapted_all, upstream_all = bytearray(), bytearray()
    numerical_failures, bit_differences, max_error = 0, 0, 0.0
    for trial in dataset["trials"]:
        payloads = [b"\x00\x7e" * 10, struct.pack("<20e", *trial["input"]), b"\x00\x7e" * 10]
        pointers = []
        try:
            for payload in payloads:
                device = C.c_void_p()
                checked(hip.hipMalloc(C.byref(device), len(payload) + 256))
                pointers.append(device)
                host = C.create_string_buffer(guard + payload + guard)
                checked(hip.hipMemcpy(device, host, len(payload) + 256, 1))
            checked(lib.run_case(*(C.c_void_p(p.value + 128) for p in pointers)))
            checked(hip.hipDeviceSynchronize())
            actuals = []
            for i, (device, payload) in enumerate(zip(pointers, payloads)):
                host = C.create_string_buffer(len(payload) + 256)
                checked(hip.hipMemcpy(host, device, len(payload) + 256, 2))
                raw = host.raw
                if raw[:128] != guard or raw[-128:] != guard:
                    raise RuntimeError("Allocation guard modified")
                actual = raw[128:-128]
                if i == 1 and actual != payload:
                    raise RuntimeError("Input bytes modified")
                actuals.append(actual)
            adapted_all.extend(actuals[0])
            upstream_all.extend(actuals[2])
            bit_differences += sum(
                actuals[0][i : i + 2] != actuals[2][i : i + 2] for i in range(0, 20, 2)
            )
            for actual in (actuals[0], actuals[2]):
                for got, expected in zip(struct.unpack("<10e", actual), trial["expected"]):
                    err = abs(got - expected)
                    max_error = max(max_error, err)
                    if not math.isfinite(got) or err > dataset["atol"] + dataset["rtol"] * abs(
                        expected
                    ):
                        numerical_failures += 1
        finally:
            for device in pointers:
                checked(hip.hipFree(device))
    (out / "adapted.bin").write_bytes(adapted_all)
    (out / "upstream.bin").write_bytes(upstream_all)
    report = {
        "status": "passed" if not bit_differences and not numerical_failures else "failed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "device": device_name.value.decode(),
        "architecture": "gfx950",
        "trials": len(dataset["trials"]),
        "launches_per_trial": 2,
        "adapted_outputs": len(adapted_all) // 2,
        "upstream_outputs": len(upstream_all) // 2,
        "adapted_upstream_bit_differences": bit_differences,
        "cpu_reference_comparisons": len(adapted_all),
        "numerical_failures": numerical_failures,
        "max_abs_error": max_error,
        "inputs_unchanged": True,
        "all_allocation_guards_unchanged": True,
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "adapted_sha256": sha(out / "adapted.bin"),
        "upstream_sha256": sha(out / "upstream.bin"),
        "binary_sha256": sha(out / "driver.so"),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": dataset["scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
