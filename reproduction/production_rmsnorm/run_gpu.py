"""Finite native RMSNorm validation, separate from the pending full Lean proof."""

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


def bit_differences(a, b):
    if len(a) != len(b):
        raise ValueError("Binary stream lengths differ")
    return sum(x != y for x, y in zip(struct.iter_unpack("<H", a), struct.iter_unpack("<H", b)))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    for name, digest in json.loads((data / "manifest.json").read_text())["files"].items():
        if sha(data / name) != digest:
            raise ValueError("Frozen input differs: " + name)
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
        "-MD",
        "-MF",
        str(out / "dependencies.d"),
        str(data / "driver.hip"),
        "-o",
        str(out / "driver.so"),
    ]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    dependencies = shlex.split(
        (out / "dependencies.d").read_text().replace("\\\n", " ").split(":", 1)[1]
    )
    headers = {str(Path(name).resolve()): sha(Path(name).resolve()) for name in dependencies}
    (out / "compiler-inputs.json").write_text(json.dumps(headers, indent=2) + "\n")
    with tarfile.open(out / "compiler-inputs.tar.gz", "w:gz") as archive:
        for name in sorted(headers):
            archive.add(name, arcname=name.lstrip("/"), recursive=False)
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
    lib.run_case.argtypes = [C.c_int, C.c_void_p, C.c_void_p, C.c_void_p, C.c_void_p]
    lib.run_case.restype = C.c_int
    lib.runtime_attribute.argtypes = [C.c_int]
    lib.runtime_attribute.restype = C.c_int
    warp, max_threads = lib.runtime_attribute(0), lib.runtime_attribute(1)
    if warp != 64 or max_threads < 1024:
        raise ValueError("Native launch contract differs")
    device_name = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device_name, len(device_name), 0))
    metadata = json.loads((data / "dataset.json").read_text())
    streams = {
        name: (data / (name + ".bin")).read_bytes()
        for name in ("input", "weight", "expected", "source-tree")
    }
    guard = b"\x5a" * 128
    cases = []
    with (
        (out / "adapted.bin").open("wb") as adapted_file,
        (out / "upstream.bin").open("wb") as upstream_file,
    ):
        for case in metadata["cases"]:
            n = case["elements"]
            result = {
                "rows": case["rows"],
                "grid": case["grid"],
                "block": 1024,
                "warp": warp,
                "trials": [],
            }
            for trial in case["trials"]:
                offset, woff = trial["offset_bytes"], trial["weight_offset_bytes"]
                inputs = streams["input"][offset : offset + n * 2]
                weight = streams["weight"][woff : woff + 16384 * 2]
                expected = streams["expected"][offset : offset + n * 2]
                tree = streams["source-tree"][offset : offset + n * 2]
                payloads = [b"\x00\x7e" * n, inputs, weight, b"\x00\x7e" * n]
                pointers = []
                try:
                    for payload in payloads:
                        ptr = C.c_void_p()
                        checked(hip.hipMalloc(C.byref(ptr), len(payload) + 256))
                        pointers.append(ptr)
                        host = C.create_string_buffer(guard + payload + guard)
                        checked(hip.hipMemcpy(ptr, host, len(payload) + 256, 1))
                    checked(
                        lib.run_case(
                            case["rows"], *(C.c_void_p(ptr.value + 128) for ptr in pointers)
                        )
                    )
                    checked(hip.hipDeviceSynchronize())
                    raw = []
                    for index, (ptr, payload) in enumerate(zip(pointers, payloads)):
                        host = C.create_string_buffer(len(payload) + 256)
                        checked(hip.hipMemcpy(host, ptr, len(payload) + 256, 2))
                        actual = host.raw
                        if actual[:128] != guard or actual[-128:] != guard:
                            raise RuntimeError("Allocation guard modified")
                        actual = actual[128:-128]
                        if index in (1, 2) and actual != payload:
                            raise RuntimeError("Input or weight modified")
                        raw.append(actual)
                    adapted_file.write(raw[0])
                    upstream_file.write(raw[3])
                    record = {
                        **trial,
                        "paired_output_values": n,
                        "cpu_reference_comparisons": n * 2,
                        "bit_differences": bit_differences(raw[0], raw[3]),
                        "source_tree_cpu_bit_differences": bit_differences(raw[0], tree),
                        "inputs_unchanged": True,
                        "weights_unchanged": True,
                        "all_allocation_guards_unchanged": True,
                    }
                    for label, actual in (("adapted", raw[0]), ("upstream", raw[3])):
                        failures, max_error = 0, 0.0
                        for (got,), (exp,) in zip(
                            struct.iter_unpack("<e", actual), struct.iter_unpack("<e", expected)
                        ):
                            error = abs(got - exp)
                            max_error = max(max_error, error)
                            if (
                                not math.isfinite(got)
                                or not math.isfinite(exp)
                                or error > metadata["atol"] + metadata["rtol"] * abs(exp)
                            ):
                                failures += 1
                        record[label + "_numerical_failures"] = failures
                        record[label + "_max_abs_error"] = max_error
                    result["trials"].append(record)
                    print(
                        json.dumps(
                            {
                                "rows": case["rows"],
                                "trial": trial["trial"],
                                "bit_differences": record["bit_differences"],
                                "adapted_numerical_failures": record["adapted_numerical_failures"],
                                "upstream_numerical_failures": record[
                                    "upstream_numerical_failures"
                                ],
                            }
                        ),
                        flush=True,
                    )
                finally:
                    for ptr in pointers:
                        checked(hip.hipFree(ptr))
            cases.append(result)
    trials = [t for c in cases for t in c["trials"]]
    failures = sum(
        t["adapted_numerical_failures"] + t["upstream_numerical_failures"] for t in trials
    )
    report = {
        "status": "passed" if not failures else "failed",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "device": device_name.value.decode(),
        "architecture": "gfx950",
        "warp": warp,
        "max_threads_per_block": max_threads,
        "cases": cases,
        "trials": len(trials),
        "launches": len(trials) * 2,
        "paired_output_values": sum(t["paired_output_values"] for t in trials),
        "cpu_reference_comparisons": sum(t["cpu_reference_comparisons"] for t in trials),
        "bit_differences": sum(t["bit_differences"] for t in trials),
        "source_tree_cpu_bit_differences": sum(
            t["source_tree_cpu_bit_differences"] for t in trials
        ),
        "numerical_failures": failures,
        "max_abs_error": max(
            t[label + "_max_abs_error"] for t in trials for label in ("adapted", "upstream")
        ),
        "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)),
        "adapted_sha256": sha(out / "adapted.bin"),
        "upstream_sha256": sha(out / "upstream.bin"),
        "binary_sha256": sha(out / "driver.so"),
        "compiler_inputs": len(headers),
        "compile_command": command,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "complete_source_proof": False,
        "certificates": 0,
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "scope": metadata["scope"],
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    files = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(files, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: report[k]
                for k in (
                    "status",
                    "trials",
                    "launches",
                    "paired_output_values",
                    "cpu_reference_comparisons",
                    "bit_differences",
                    "source_tree_cpu_bit_differences",
                    "numerical_failures",
                    "max_abs_error",
                )
            }
        ),
        flush=True,
    )
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
