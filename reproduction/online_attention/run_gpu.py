"""Run bounded native checks of the frozen upstream FP32 online-attention kernel."""

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
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    manifest = json.loads((data / "manifest.json").read_text())
    if any(sha(data / name) != digest for name, digest in manifest.items()):
        raise ValueError("Frozen input differs")
    meta = json.loads((data / "dataset.json").read_text())
    if sha(data / "upstream_context.cuh") != meta["upstream_definition_sha256"]:
        raise ValueError("Extracted source differs")
    out.mkdir(parents=True, exist_ok=False)
    command = ["hipcc", "-O3", "-std=c++17", "-shared", "-fPIC", "-ffp-contract=off",
               "--offload-arch=gfx950", "-MD", "-MF", str(out / "dependencies.d"),
               str(data / "driver.hip"), "-o", str(out / "driver.so")]
    result = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("HIP build failed: " + result.stderr)
    inputs = shlex.split((out / "dependencies.d").read_text().replace("\\\n", " ").split(":", 1)[1])
    headers = {str(Path(p).resolve()): sha(Path(p).resolve()) for p in inputs}
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
    guard_record = {"free_bytes": free.value, "total_bytes": total.value, "minimum_free_fraction": 0.98}
    write(out / "memory-guard.json", guard_record)
    if free.value < 0.98 * total.value:
        raise RuntimeError("Selected GPU is occupied; no trials executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_case.argtypes = [C.c_int] * 4 + [C.c_void_p] * 6
    lib.run_case.restype = C.c_int
    lib.runtime_attribute.argtypes = [C.c_int]; lib.runtime_attribute.restype = C.c_int
    warp, threads, shared = (lib.runtime_attribute(i) for i in range(3))
    if warp != 64 or threads < 32 or shared < max(c["shared_bytes"] for c in meta["cases"]):
        raise ValueError("Native device cannot support the frozen launch")
    name = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(name, len(name), 0))
    streams = {key: (data / (key + ".bin")).read_bytes() for key in ("q", "k", "v", "expected")}
    count = 0
    for case in meta["cases"]:
        dims = [case[k] for k in ("batch", "heads", "n", "d")]
        if (any(type(d) is not int or d <= 0 for d in dims)
                or case["n"] % 32 or case["d"] > 256 or case["block"] != 32
                or case["elements"] != math.prod(dims)
                or case["rows"] != math.prod(dims[:3])
                or case["offset_elements"] != count):
            raise ValueError("Frozen case dimensions or offsets differ")
        count += case["elements"]
    if any(len(streams[k]) != count * (8 if k == "expected" else 4) for k in streams):
        raise ValueError("Frozen stream length differs")
    guard = b"\x5a" * 128
    records = []
    with (out / "outputs.bin").open("wb") as outputs:
        for case in meta["cases"]:
            n, rows, offset = case["elements"], case["rows"], case["offset_elements"]
            if case["n"] % 32 or case["block"] != 32:
                raise ValueError("Upstream has no partial-tile bounds guards")
            payloads = [streams[k][offset * 4 : (offset + n) * 4] for k in ("q", "k", "v")]
            payloads += [b"\x00\x00\xc0\x7f" * rows] * 2 + [b"\x00\x00\xc0\x7f" * n]
            pointers = []
            try:
                for payload in payloads:
                    pointer = C.c_void_p()
                    checked(hip.hipMalloc(C.byref(pointer), len(payload) + 256))
                    pointers.append(pointer)
                    host = C.create_string_buffer(guard + payload + guard)
                    checked(hip.hipMemcpy(pointer, host, len(payload) + 256, 1))
                checked(lib.run_case(case["batch"], case["heads"], case["n"], case["d"],
                                     *(C.c_void_p(p.value + 128) for p in pointers)))
                checked(hip.hipDeviceSynchronize())
                actuals = []
                for i, (pointer, payload) in enumerate(zip(pointers, payloads)):
                    host = C.create_string_buffer(len(payload) + 256)
                    checked(hip.hipMemcpy(host, pointer, len(payload) + 256, 2))
                    if host.raw[:128] != guard or host.raw[-128:] != guard:
                        raise RuntimeError("Allocation guard modified")
                    actual = host.raw[128:-128]
                    if i < 3 and actual != payload:
                        raise RuntimeError("Read-only input modified")
                    actuals.append(actual)
                expected = streams["expected"][offset * 8 : (offset + n) * 8]
                failures, max_error = 0, 0.0
                for (got,), (want,) in zip(struct.iter_unpack("<f", actuals[5]), struct.iter_unpack("<d", expected)):
                    error = abs(got - want)
                    if not math.isfinite(got) or not math.isfinite(want) or error > meta["atol"] + meta["rtol"] * abs(want):
                        failures += 1
                    max_error = max(max_error, error)
                denominator = [x[0] for x in struct.iter_unpack("<f", actuals[3])]
                maximum = [x[0] for x in struct.iter_unpack("<f", actuals[4])]
                if any(not math.isfinite(x) or x <= 0 for x in denominator) or any(not math.isfinite(x) for x in maximum):
                    raise RuntimeError("Nonfinite accumulator or nonpositive denominator")
                outputs.write(actuals[5])
                record = {**case, "output_comparisons": n, "numerical_failures": failures,
                          "max_abs_error": max_error, "inputs_unchanged": True,
                          "allocation_guards_unchanged": True, "all_denominators_positive": True,
                          "all_accumulator_maxima_finite": True}
                records.append(record)
                print(json.dumps(record), flush=True)
            finally:
                for pointer in pointers:
                    checked(hip.hipFree(pointer))
    report = {
        "schema": 1, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "device": name.value.decode(), "warp": warp, "shared_per_block": shared,
        "compiler_command": command, "compiler_input_files": len(headers),
        "input_manifest_sha256": sha(data / "manifest.json"), "cases": records,
        "trials": len(records), "forward_kernel_launches": len(records),
        "initialization_kernel_launches": len(records),
        "output_comparisons": sum(r["output_comparisons"] for r in records),
        "numerical_failures": sum(r["numerical_failures"] for r in records),
        "max_abs_error": max(r["max_abs_error"] for r in records),
        "atol": meta["atol"], "rtol": meta["rtol"],
        "source_certificates": 0, "whole_kernel_execution_proved": False,
        "race_freedom_proved": False, "ieee_equivalence_proved": False,
        "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    write(out / "results.json", report)
    write(out / "manifest.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    if report["numerical_failures"]:
        raise RuntimeError("Numerical comparison failures; artifacts preserved")


if __name__ == "__main__":
    main()
