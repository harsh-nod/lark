"""Execute frozen native in-place sources; numerical auditing is separate."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import tarfile


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    for name, digest in json.loads((data / "manifest.json").read_text())["files"].items():
        if sha(data / name) != digest:
            raise ValueError("Frozen input differs: " + name)
    out.mkdir(parents=True, exist_ok=False)
    command = ["hipcc", "-O3", "-std=c++17", "-shared", "-fPIC", "-ffp-contract=off",
               "--offload-arch=gfx950", "-MD", "-MF", str(out / "dependencies.d"),
               str(data / "driver.hip"), "-o", str(out / "driver.so")]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    paths = shlex.split((out / "dependencies.d").read_text().replace("\\\n", " ").split(":", 1)[1])
    headers = {str(Path(p).resolve()): sha(Path(p).resolve()) for p in paths}
    (out / "compiler-inputs.json").write_text(json.dumps(headers, indent=2) + "\n")
    with tarfile.open(out / "compiler-inputs.tar.gz", "w:gz") as archive:
        for name in sorted(headers):
            archive.add(name, arcname=name.lstrip("/"), recursive=False)

    hip = C.CDLL("/opt/rocm/lib/libamdhip64.so")
    hip.hipGetErrorString.argtypes, hip.hipGetErrorString.restype = [C.c_int], C.c_char_p
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
    memory = {"free_bytes": free.value, "total_bytes": total.value, "minimum_free_fraction": .98}
    (out / "memory-guard.json").write_text(json.dumps(memory, indent=2) + "\n")
    if free.value < .98 * total.value:
        raise RuntimeError("Selected GPU is occupied; no trial executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_case.argtypes, lib.run_case.restype = [C.c_int] + [C.c_void_p] * 5, C.c_int
    lib.runtime_attribute.argtypes, lib.runtime_attribute.restype = [C.c_int], C.c_int
    attributes = [lib.runtime_attribute(i) for i in range(3)]
    if attributes[0] != 64 or attributes[1] < 1024 or attributes[2] < (32 + 16384) * 4:
        raise ValueError("Native geometry/shared-memory contract unavailable")
    device = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device, len(device), 0))
    metadata = json.loads((data / "dataset.json").read_text())
    streams = {name: (data / (name + ".bin")).open("rb") for name in ("input", "residual", "weight")}
    outputs = {name: (out / (name + ".bin")).open("wb") for name in
               ("adapted-input", "adapted-residual", "upstream-input", "upstream-residual")}
    guard = b"\x5a" * 128
    records = []
    try:
        for case in metadata["cases"]:
            n = case["elements"]
            for trial in case["trials"]:
                offset = trial["offset_elements"] * 2
                payload = {}
                for name in ("input", "residual"):
                    streams[name].seek(offset)
                    payload[name] = streams[name].read(n * 2)
                    if len(payload[name]) != n * 2:
                        raise ValueError("Truncated in-out input")
                streams["weight"].seek(trial["weight_offset_bytes"])
                weight = streams["weight"].read(16384 * 2)
                if len(weight) != 16384 * 2:
                    raise ValueError("Truncated weight input")
                initial = [payload["input"], payload["residual"], weight,
                           payload["input"], payload["residual"]]
                pointers = []
                try:
                    for raw in initial:
                        ptr = C.c_void_p()
                        checked(hip.hipMalloc(C.byref(ptr), len(raw) + 256))
                        pointers.append(ptr)
                        host = C.create_string_buffer(guard + raw + guard)
                        checked(hip.hipMemcpy(ptr, host, len(raw) + 256, 1))
                    checked(lib.run_case(case["rows"], *(C.c_void_p(p.value + 128) for p in pointers)))
                    checked(hip.hipDeviceSynchronize())
                    results = []
                    for index, (ptr, raw) in enumerate(zip(pointers, initial)):
                        host = C.create_string_buffer(len(raw) + 256)
                        checked(hip.hipMemcpy(host, ptr, len(raw) + 256, 2))
                        actual = host.raw
                        if actual[:128] != guard or actual[-128:] != guard:
                            raise RuntimeError("Allocation guard changed")
                        actual = actual[128:-128]
                        if index == 2 and actual != raw:
                            raise RuntimeError("Read-only weight changed")
                        results.append(actual)
                    for name, index in [("adapted-input", 0), ("adapted-residual", 1),
                                        ("upstream-input", 3), ("upstream-residual", 4)]:
                        outputs[name].write(results[index])
                    records.append({"rows": case["rows"], **trial, "elements_per_buffer": n,
                                    "all_allocation_guards_unchanged": True, "weight_unchanged": True})
                    print(json.dumps({"rows": case["rows"], "trial": trial["trial"],
                                      "status": "runtime-checks-passed"}), flush=True)
                finally:
                    for ptr in pointers:
                        checked(hip.hipFree(ptr))
    finally:
        for stream in list(streams.values()) + list(outputs.values()):
            stream.close()
    report = {
        "schema": 1, "status": "runtime-checks-passed-pending-independent-numerical-audit",
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(), "device": device.value.decode(),
        "architecture": "gfx950", "warp": attributes[0], "block": 1024,
        "shared_bytes": (32 + 16384) * 4, "trials": len(records), "launches": len(records) * 2,
        "output_elements_per_method_per_buffer": sum(r["elements_per_buffer"] for r in records),
        "cases": records, "input_manifest_sha256": sha(data / "manifest.json"),
        "runner_sha256": sha(Path(__file__)), "binary_sha256": sha(out / "driver.so"),
        "output_sha256": {name: sha(out / (name + ".bin")) for name in outputs},
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "compiler_inputs": len(headers), "compile_command": command,
        "comparison_template_body_retained": True, "comparison_helpers_replaced_for_hip": True,
        "original_nvidia_kernel_executed": False, "source_certificates": 0,
        "whole_kernel_execution_proved": False, "actual_trace_classification_proved": False,
        "ieee_equivalence_proved": False, "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest = {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "trials", "launches", "output_elements_per_method_per_buffer")}), flush=True)


if __name__ == "__main__":
    main()
