"""Run complete native in-place RoPE and retained helpers on a free AMD GPU."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import struct
import subprocess
import tarfile


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    for name, expected in json.loads((data / "manifest.json").read_text())["files"].items():
        if sha(data / name) != expected:
            raise ValueError("Frozen input differs: " + name)
    out.mkdir(parents=True, exist_ok=False)
    command = ["hipcc", "-O3", "-std=c++17", "-shared", "-fPIC", "-ffp-contract=off",
               "--offload-arch=gfx950", "-MD", "-MF", str(out / "dependencies.d"),
               str(data / "driver.hip"), "-o", str(out / "driver.so")]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out / "build.log").write_text(built.stdout + built.stderr)
    if built.returncode:
        raise RuntimeError(built.stderr)
    dependencies = shlex.split((out / "dependencies.d").read_text().replace("\\\n", " ").split(":", 1)[1])
    headers = {str(Path(p).resolve()): sha(Path(p).resolve()) for p in dependencies}
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
    (out / "memory-guard.json").write_text(json.dumps({"free_bytes": free.value, "total_bytes": total.value,
                                                      "minimum_free_fraction": .98}, indent=2) + "\n")
    if free.value < .98 * total.value:
        raise RuntimeError("Selected GPU is occupied; no trial executed")
    lib = C.CDLL(str(out / "driver.so"))
    lib.run_case.argtypes, lib.run_case.restype = [C.c_int, C.c_int] + [C.c_void_p] * 6, C.c_int
    lib.runtime_attribute.argtypes, lib.runtime_attribute.restype = [C.c_int], C.c_int
    if lib.runtime_attribute(0) != 64 or lib.runtime_attribute(1) < 512:
        raise RuntimeError("Native wave64/block512 geometry unavailable")
    device = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device, len(device), 0))
    metadata = json.loads((data / "dataset.json").read_text())
    inputs = {name: (data / (name + ".bin")).open("rb") for name in ("query", "key", "cache")}
    outputs = {f"{layout}-{method}-{name}": (out / f"{layout}-{method}-{name}.bin").open("wb")
               for layout in metadata["layouts"] for method in ("adapted", "upstream") for name in ("query", "key")}
    records, guard = [], b"\x5a" * 128
    try:
        for case in metadata["cases"]:
            rows = case["rows"]
            payload = {}
            for name, heads in (("query", 32), ("key", 8), ("cache", 1)):
                inputs[name].seek(case["offset_bytes"][name])
                raw = inputs[name].read(rows * heads * 128 * 2)
                if len(raw) != rows * heads * 128 * 2 or hashlib.sha256(raw).hexdigest() != case["sha256"][name]:
                    raise ValueError("Case input differs: " + name)
                payload[name] = raw
            positions = b"".join(struct.pack("<q", i) for i in range(rows))
            for layout in metadata["layouts"]:
                initial = [payload["query"], payload["key"], payload["cache"],
                           payload["query"], payload["key"], positions]
                pointers, result = [], []
                try:
                    for raw in initial:
                        ptr = C.c_void_p()
                        checked(hip.hipMalloc(C.byref(ptr), len(raw) + 256))
                        pointers.append(ptr)
                        host = C.create_string_buffer(guard + raw + guard)
                        checked(hip.hipMemcpy(ptr, host, len(raw) + 256, 1))
                    checked(lib.run_case(int(layout == "split-half"), rows,
                                        *(C.c_void_p(p.value + 128) for p in pointers)))
                    checked(hip.hipDeviceSynchronize())
                    for index, (ptr, raw) in enumerate(zip(pointers, initial)):
                        host = C.create_string_buffer(len(raw) + 256)
                        checked(hip.hipMemcpy(host, ptr, len(raw) + 256, 2))
                        actual = host.raw
                        if actual[:128] != guard or actual[-128:] != guard:
                            raise RuntimeError("Allocation guard changed")
                        actual = actual[128:-128]
                        if index in (2, 5) and actual != raw:
                            raise RuntimeError("Read-only cache/positions changed")
                        result.append(actual)
                    for method, names in (("adapted", (("query", 0), ("key", 1))),
                                          ("upstream", (("query", 3), ("key", 4)))):
                        for name, index in names:
                            outputs[f"{layout}-{method}-{name}"].write(result[index])
                    records.append({"rows": rows, "trial": case["trial"], "layout": layout,
                                    "all_allocation_guards_unchanged": True, "cache_unchanged": True,
                                    "positions_unchanged": True, "query_elements": rows * 4096,
                                    "key_elements": rows * 1024})
                    print(json.dumps({"rows": rows, "trial": case["trial"], "layout": layout,
                                      "status": "runtime-checks-passed"}), flush=True)
                finally:
                    for ptr in pointers:
                        checked(hip.hipFree(ptr))
    finally:
        for stream in list(inputs.values()) + list(outputs.values()):
            stream.close()
    report = {
        "schema": 1, "status": "runtime-checks-passed-pending-independent-numerical-audit",
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(), "device": device.value.decode(),
        "architecture": "gfx950", "warp": 64, "block": 512, "cases": records,
        "trials": len(records), "launches": len(records) * 2,
        "output_elements_per_method": sum(r["query_elements"] + r["key_elements"] for r in records),
        "input_manifest_sha256": sha(data / "manifest.json"), "runner_sha256": sha(Path(__file__)),
        "binary_sha256": sha(out / "driver.so"),
        "output_sha256": {name: sha(out / (name + ".bin")) for name in outputs},
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "compiler_inputs": len(headers), "compile_command": command,
        "upstream_device_bodies_retained": True, "VLLM_LDG_replaced_with_plain_hip_load": True,
        "original_nvidia_kernel_executed": False, "whole_kernel_execution_proved": False,
        "actual_trace_classification_proved": False, "source_certificates": 0,
        "model_calls": 0, "original_paper_fully_reproduced": False,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest = {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "trials", "launches", "output_elements_per_method")}), flush=True)


if __name__ == "__main__":
    main()
