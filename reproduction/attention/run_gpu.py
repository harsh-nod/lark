"""Validate the full-size certified scalar attention, preserving inputs and red zones."""

import argparse
import ctypes as C
import ctypes.util
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import struct
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from reproduction.attention.bundle import validate_bundle
from reproduction.attention.bundle import load_dataset, PackedValues


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--arch", default="gfx950")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    dataset_path = args.input / "cases.json"
    index_path = args.input / "certificate-index.json"
    source = args.input / "certified.hip"
    data = load_dataset(args.input)
    index = json.loads(index_path.read_text())
    validate_bundle(data, index, source.read_text())
    library = args.output / "certified.so"
    command = [
        "hipcc",
        "-O3",
        "-std=c++17",
        "-shared",
        "-fPIC",
        "-ffp-contract=off",
        "--offload-arch=" + args.arch,
        str(source.resolve()),
        "-o",
        str(library.resolve()),
    ]
    result = subprocess.run(command, text=True, capture_output=True, timeout=120)
    (args.output / "build.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(result.stderr)
    lib = C.CDLL(str(library.resolve()))
    runtime = C.util.find_library("amdhip64") or "/opt/rocm/lib/libamdhip64.so"
    hip = C.CDLL(runtime)
    hip.hipGetErrorString.argtypes = [C.c_int]
    hip.hipGetErrorString.restype = C.c_char_p
    hip.hipMalloc.argtypes = [C.POINTER(C.c_void_p), C.c_size_t]
    hip.hipMemcpy.argtypes = [C.c_void_p, C.c_void_p, C.c_size_t, C.c_int]
    hip.hipFree.argtypes = [C.c_void_p]
    hip.hipDeviceSynchronize.argtypes = []
    hip.hipDeviceGetName.argtypes = [C.c_char_p, C.c_int, C.c_int]
    lib.run_case.argtypes = [C.c_int, C.POINTER(C.c_void_p), C.c_void_p]
    lib.run_case.restype = C.c_int

    def checked(code):
        if code:
            raise RuntimeError(hip.hipGetErrorString(code).decode())

    def upload(payload):
        device = C.c_void_p()
        checked(hip.hipMalloc(C.byref(device), len(payload)))
        host = C.create_string_buffer(payload)
        checked(hip.hipMemcpy(device, host, len(payload), 1))
        return device

    def download(device, size):
        host = C.create_string_buffer(size)
        checked(hip.hipMemcpy(host, device, size, 2))
        return host.raw

    name = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(name, len(name), 0))
    report = {
        "schema": 1,
        "status": "running",
        "experiment": "attention-pipeline-v12-exact-source",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": name.value.decode(),
        "architecture": args.arch,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "runner_sha256": sha(Path(__file__)),
        "dataset_sha256": sha(dataset_path),
        "tensor_data_sha256": data["tensor_data_sha256"],
        "certificate_index_sha256": sha(index_path),
        "wrapper_sha256": sha(source),
        "library_sha256": sha(library),
        "compile_command": command,
        "model_calls": 0,
        "reference": data["reference"],
        "cases": [],
        "scope": "Full three-launch dense SDPA/GQA, exact certified sources and intermediate wiring, one thread per output. Abstract operation proof plus separate finite numerical checks; not the paper's optimized source or launch.",
    }
    guard = bytes([0x5A]) * 128

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    save()
    for case_id, row in enumerate(data["cases"]):
        result = {"key": row["key"], "certificate": index[row["key"]], "trials": []}
        for trial in row["trials"]:
            allocations, payloads = [], []
            try:
                for buffer in trial["buffers"]:
                    values = (
                        buffer["values"]
                        if buffer["role"] == "input"
                        else [float("nan")] * buffer["size"]
                    )
                    payload = (
                        bytes(values.payload)
                        if isinstance(values, PackedValues)
                        else struct.pack(
                            "<" + ("e" if buffer["dtype"] == "float16" else "f") * len(values),
                            *values,
                        )
                    )
                    payloads.append(payload)
                    allocations.append(upload(guard + payload + guard))
                pointers = (C.c_void_p * len(allocations))(
                    *(C.c_void_p(device.value + len(guard)) for device in allocations)
                )
                checked(lib.run_case(case_id, pointers, None))
                checked(hip.hipDeviceSynchronize())
                max_error = {"float16": 0.0, "float32": 0.0}
                for buffer, device, payload in zip(trial["buffers"], allocations, payloads):
                    received = download(device, len(payload) + 2 * len(guard))
                    if received[: len(guard)] != guard or received[-len(guard) :] != guard:
                        raise RuntimeError("Guard zone overwritten")
                    actual = received[len(guard) : -len(guard)]
                    if buffer["role"] == "input":
                        if actual != payload:
                            raise RuntimeError("Input bytes modified")
                    else:
                        values = struct.unpack(
                            "<" + ("e" if buffer["dtype"] == "float16" else "f") * buffer["size"],
                            actual,
                        )
                        for value, expected in zip(values, buffer["expected"]):
                            error = abs(value - expected)
                            if not math.isfinite(value) or error > row["tolerances"][
                                buffer["dtype"]
                            ]["atol"] + row["tolerances"][buffer["dtype"]]["rtol"] * abs(expected):
                                raise RuntimeError(f"{row['key']}: {value} differs from {expected}")
                            max_error[buffer["dtype"]] = max(max_error[buffer["dtype"]], error)
                result["trials"].append(
                    {
                        "trial": trial["trial"],
                        "max_abs_error": max_error,
                        "inputs_unchanged": True,
                        "guard_zones_unchanged": True,
                        "scalar_comparisons": sum(
                            b["size"] for b in trial["buffers"] if b["role"] != "input"
                        ),
                        "intermediate_comparisons": sum(
                            b["size"] for b in trial["buffers"] if b["role"] == "scratch"
                        ),
                        "final_comparisons": trial["buffers"][-1]["size"],
                    }
                )
            finally:
                for device in allocations:
                    checked(hip.hipFree(device))
        result["status"] = "passed"
        report["cases"].append(result)
        save()
    report["status"] = "passed"
    save()
    print(
        json.dumps(
            {
                "status": "passed",
                "device": report["device"],
                "trials": sum(len(c["trials"]) for c in report["cases"]),
                "scalar_comparisons": sum(
                    t["scalar_comparisons"] for c in report["cases"] for t in c["trials"]
                ),
            }
        )
    )


if __name__ == "__main__":
    main()
