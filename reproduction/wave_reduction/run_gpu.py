"""Run the exact certified HIP wave reduction; keep cancellation stress separate."""

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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest = json.loads((data / "manifest.json").read_text())
    for name, h in manifest["files"].items():
        if sha(data / name) != h:
            raise ValueError("Input differs: " + name)
    out.mkdir(parents=True, exist_ok=False)
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-shared",
        "-fPIC",
        "-ffp-contract=off",
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
    memory = {"free_bytes": free.value, "total_bytes": total.value, "minimum_free_fraction": 0.98}
    (out / "memory-guard.json").write_text(json.dumps(memory, indent=2) + "\n")
    if free.value < total.value * 0.98:
        raise RuntimeError("Selected GPU is occupied; no trials executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.runtime_attribute.argtypes = [C.c_int]
    lib.runtime_attribute.restype = C.c_int
    if lib.runtime_attribute(0) != 64 or lib.runtime_attribute(1) < 64:
        raise RuntimeError("Native wave/launch contract differs")
    lib.launch_wave.argtypes = [C.c_void_p, C.c_void_p]
    lib.launch_wave.restype = C.c_int
    device = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device, len(device), 0))
    metadata = json.loads((data / "dataset.json").read_text())
    inputs, expected, source_tree = [
        (data / n).read_bytes() for n in ("input.bin", "reference.bin", "source-tree.bin")
    ]
    if (
        len(inputs) != len(expected)
        or len(inputs) != len(source_tree)
        or len(inputs) != len(metadata["trials"]) * 256
    ):
        raise ValueError("Dataset lengths differ")
    guard = b"\x5a" * 128
    outputs, records = bytearray(), []
    for entry in metadata["trials"]:
        offset = entry["trial"] * 256
        x, ref, tree = (
            inputs[offset : offset + 256],
            expected[offset : offset + 256],
            source_tree[offset : offset + 256],
        )
        pointers = []
        try:
            payloads = [x, b"\x00\x00\xc0\x7f" * 64]
            for payload in payloads:
                pointer = C.c_void_p()
                checked(hip.hipMalloc(C.byref(pointer), 512))
                pointers.append(pointer)
                host = C.create_string_buffer(guard + payload + guard)
                checked(hip.hipMemcpy(pointer, host, 512, 1))
            checked(lib.launch_wave(*(C.c_void_p(p.value + 128) for p in pointers)))
            checked(hip.hipDeviceSynchronize())
            raw = []
            for index, pointer in enumerate(pointers):
                host = C.create_string_buffer(512)
                checked(hip.hipMemcpy(host, pointer, 512, 2))
                if host.raw[:128] != guard or host.raw[-128:] != guard:
                    raise RuntimeError("Allocation guard modified")
                payload = host.raw[128:-128]
                if index == 0 and payload != x:
                    raise RuntimeError("Input changed")
                raw.append(payload)
            actual = raw[1]
            outputs.extend(actual)
            bit_differences = sum(actual[i : i + 4] != tree[i : i + 4] for i in range(0, 256, 4))
            failures, max_error = 0, 0.0
            for got, wanted in zip(struct.unpack("<64f", actual), struct.unpack("<64f", ref)):
                error = abs(got - wanted)
                max_error = max(max_error, error)
                if not math.isfinite(got) or error > metadata["atol"] + metadata["rtol"] * abs(
                    wanted
                ):
                    failures += 1
            records.append(
                {
                    **entry,
                    "output_values": 64,
                    "source_tree_bit_differences": bit_differences,
                    "reference_numerical_failures": failures,
                    "max_abs_reference_error": max_error,
                    "inputs_unchanged": True,
                    "all_allocation_guards_unchanged": True,
                }
            )
        finally:
            for pointer in pointers:
                checked(hip.hipFree(pointer))
    (out / "output.bin").write_bytes(outputs)
    ordinary = [r for r in records if not r["stress"]]
    stress = [r for r in records if r["stress"]]
    bit_differences = sum(r["source_tree_bit_differences"] for r in records)
    ordinary_failures = sum(r["reference_numerical_failures"] for r in ordinary)
    stress_differences = sum(r["reference_numerical_failures"] for r in stress)
    passed = (
        not bit_differences
        and not ordinary_failures
        and stress_differences == metadata["stress_source_tree_reference_differences"]
    )
    report = {
        "status": "passed" if passed else "failed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "device": device.value.decode(),
        "architecture": "gfx950",
        "warp": 64,
        "max_threads_per_block": lib.runtime_attribute(1),
        "trials": records,
        "ordinary_trials": len(ordinary),
        "stress_trials": len(stress),
        "kernel_launches": len(records),
        "output_values": len(outputs) // 4,
        "source_tree_bit_differences": bit_differences,
        "ordinary_reference_comparisons": len(ordinary) * 64,
        "ordinary_reference_numerical_failures": ordinary_failures,
        "ordinary_max_abs_reference_error": max(r["max_abs_reference_error"] for r in ordinary),
        "stress_reference_disagreements": stress_differences,
        "stress_max_abs_reference_error": max(r["max_abs_reference_error"] for r in stress),
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "output_sha256": sha(out / "output.bin"),
        "binary_sha256": sha(out / "driver.so"),
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "compile_command": command,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "stress_scope": metadata["stress_scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: report[k]
                for k in (
                    "status",
                    "device",
                    "ordinary_trials",
                    "stress_trials",
                    "output_values",
                    "source_tree_bit_differences",
                    "ordinary_reference_numerical_failures",
                    "stress_reference_disagreements",
                )
            }
        )
    )
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
