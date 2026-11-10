"""Validate frozen native FP16 and extracted upstream FP32 online kernels."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import shlex
import struct
import subprocess
import tarfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    files = json.loads((data / "manifest.json").read_text())
    if any(Path(n).name != n or sha(data / n) != h for n, h in files.items()):
        raise ValueError("Frozen input differs")
    meta = json.loads((data / "dataset.json").read_text())
    if sha(data / "kernel.hip") != meta["native_source_sha256"] or sha(data / "upstream_context.cuh") != meta["upstream_definition_sha256"]:
        raise ValueError("Source identity differs")
    out.mkdir(parents=True, exist_ok=False)
    command = ["hipcc", "-O3", "-std=c++17", "-shared", "-fPIC", "-ffp-contract=off",
               "--offload-arch=gfx950", "-MD", "-MF", str(out / "dependencies.d"),
               str(data / "native_driver.hip"), "-o", str(out / "driver.so")]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError("HIP build failed: " + built.stderr)
    headers = {str(Path(n).resolve()): sha(Path(n).resolve()) for n in
               shlex.split((out / "dependencies.d").read_text().replace("\\\n", " ").split(":", 1)[1])}
    write(out / "compiler-inputs.json", headers)
    with tarfile.open(out / "compiler-inputs.tar.gz", "w:gz") as archive:
        for name in sorted(headers):
            archive.add(name, arcname=name.lstrip("/"), recursive=False)
    hip = C.CDLL("/opt/rocm/lib/libamdhip64.so")
    hip.hipGetErrorString.argtypes = [C.c_int]; hip.hipGetErrorString.restype = C.c_char_p
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
    write(out / "memory-guard.json", {"free_bytes": free.value, "total_bytes": total.value, "minimum_free_fraction": 0.98})
    if free.value < total.value * 0.98:
        raise RuntimeError("Selected GPU memory is occupied; no trials executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_native_case.argtypes = [C.c_int] + [C.c_void_p] * 10
    lib.run_native_case.restype = C.c_int
    lib.runtime_attribute.argtypes = [C.c_int]; lib.runtime_attribute.restype = C.c_int
    if lib.runtime_attribute(0) != 64 or lib.runtime_attribute(2) < 102400:
        raise ValueError("Native wave64/LDS requirements differ")
    device = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device, len(device), 0))
    names = ("query", "key", "value", "qf", "kf", "vf", "expected")
    streams = {n: (data / (n + ".bin")).read_bytes() for n in names}
    count = 0
    for case in meta["cases"]:
        if (type(case["groups"]) is not int or case["groups"] not in (1, 3)
                or case["n"] != 128 or case["d"] != 256 or case["tile"] != 32
                or case["elements"] != case["groups"] * 32768 or case["offset_elements"] != count):
            raise ValueError("Frozen case shape differs")
        count += case["elements"]
    if any(len(v) != count * (8 if k == "expected" else 4 if len(k) == 2 else 2) for k, v in streams.items()):
        raise ValueError("Frozen stream extent differs")
    guard = b"\x5a" * 128
    records = []
    with (out / "adapted.bin").open("wb") as adapted, (out / "upstream.bin").open("wb") as upstream:
        for case in meta["cases"]:
            n, offset = case["elements"], case["offset_elements"]
            rows = case["groups"] * 128
            payloads = [b"\x00\x7e" * n]
            payloads += [streams[k][offset * 2:(offset + n) * 2] for k in ("query", "key", "value")]
            payloads += [b"\x00\x00\xc0\x7f" * n]
            payloads += [streams[k][offset * 4:(offset + n) * 4] for k in ("qf", "kf", "vf")]
            payloads += [b"\x00\x00\xc0\x7f" * rows] * 2
            pointers = []
            try:
                for payload in payloads:
                    pointer = C.c_void_p()
                    checked(hip.hipMalloc(C.byref(pointer), len(payload) + 256))
                    pointers.append(pointer)
                    host = C.create_string_buffer(guard + payload + guard)
                    checked(hip.hipMemcpy(pointer, host, len(payload) + 256, 1))
                checked(lib.run_native_case(case["groups"], *(C.c_void_p(p.value + 128) for p in pointers)))
                checked(hip.hipDeviceSynchronize())
                actuals = []
                for i, (pointer, payload) in enumerate(zip(pointers, payloads)):
                    host = C.create_string_buffer(len(payload) + 256)
                    checked(hip.hipMemcpy(host, pointer, len(payload) + 256, 2))
                    if host.raw[:128] != guard or host.raw[-128:] != guard:
                        raise RuntimeError("Allocation guard changed")
                    raw = host.raw[128:-128]
                    if i in (1, 2, 3, 5, 6, 7) and raw != payload:
                        raise RuntimeError("Read-only input changed")
                    actuals.append(raw)
                expected = streams["expected"][offset * 8:(offset + n) * 8]
                record = {**case, "paired_output_values": n, "cpu_reference_comparisons": 2 * n,
                          "inputs_unchanged": True, "allocation_guards_unchanged": True}
                for label, raw, fmt in (("adapted", actuals[0], "<e"), ("upstream", actuals[4], "<f")):
                    failures, maximum = 0, 0.0
                    for (got,), (want,) in zip(struct.iter_unpack(fmt, raw), struct.iter_unpack("<d", expected)):
                        error = abs(got - want)
                        if not math.isfinite(got) or not math.isfinite(want) or error > meta[label + "_atol"] + meta[label + "_rtol"] * abs(want):
                            failures += 1
                        maximum = max(maximum, error)
                    record[label + "_numerical_failures"] = failures
                    record[label + "_max_abs_error"] = maximum
                l = [v[0] for v in struct.iter_unpack("<f", actuals[8])]
                m = [v[0] for v in struct.iter_unpack("<f", actuals[9])]
                if any(not math.isfinite(v) or v <= 0 for v in l) or any(not math.isfinite(v) for v in m):
                    raise RuntimeError("Invalid upstream final accumulator")
                record["upstream_final_denominators_positive"] = True
                record["upstream_final_maxima_finite"] = True
                adapted.write(actuals[0]); upstream.write(actuals[4])
                records.append(record)
                print(json.dumps(record), flush=True)
            finally:
                for pointer in pointers:
                    checked(hip.hipFree(pointer))
    report = {"schema": 1, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
              "device": device.value.decode(), "warp": 64, "native_block": 32,
              "shared_per_block": lib.runtime_attribute(2), "compiler_command": command,
              "compiler_input_files": len(headers), "input_manifest_sha256": sha(data / "manifest.json"),
              "cases": records, "trials": len(records), "adapted_launches": len(records),
              "upstream_forward_launches": len(records), "explicit_upstream_initialization_launches": len(records),
              "paired_output_values": count, "cpu_reference_comparisons": 2 * count,
              "adapted_numerical_failures": sum(r["adapted_numerical_failures"] for r in records),
              "upstream_numerical_failures": sum(r["upstream_numerical_failures"] for r in records),
              "adapted_max_abs_error": max(r["adapted_max_abs_error"] for r in records),
              "upstream_max_abs_error": max(r["upstream_max_abs_error"] for r in records),
              "source_certificates": 0, "whole_kernel_execution_proved": False,
              "actual_trace_classification_proved": False, "ieee_equivalence_proved": False,
              "model_calls": 0, "original_paper_fully_reproduced": False}
    write(out / "results.json", report)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    if report["adapted_numerical_failures"] or report["upstream_numerical_failures"]:
        raise RuntimeError("Numerical failures; all completed artifacts retained")


if __name__ == "__main__":
    main()
