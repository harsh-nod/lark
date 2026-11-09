"""Execute certified source bytes and scalar/conversion probes with HIP and stdlib Python."""

import argparse
import ctypes as C
import ctypes.util
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import random
import struct
import subprocess

if __package__:
    from .gpu_bundle import validate_bundle
else:
    from gpu_bundle import validate_bundle


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def packed(values, kind):
    return struct.pack("<" + kind * len(values), *values)


def unpacked(payload, kind):
    return list(struct.unpack("<" + kind * (len(payload) // struct.calcsize(kind)), payload))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--certificate-index", type=Path, required=True)
    p.add_argument("--calibration", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--arch", default="gfx950")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    dataset = json.loads((args.input / "cases.json").read_text())
    index = json.loads(args.certificate_index.read_text())
    validate_bundle(dataset, index, (args.input / "certified.hip").read_text())
    root = Path(__file__).resolve().parent
    libraries = []
    commands = []
    for source, name in [
        (args.input / "certified.hip", "certified"),
        (root / "probes.hip", "probes"),
    ]:
        target = args.output / (name + ".so")
        cmd = [
            "hipcc",
            "-O3",
            "-std=c++17",
            "-shared",
            "-fPIC",
            "-ffp-contract=off",
            "--offload-arch=" + args.arch,
            str(source.resolve()),
            "-o",
            str(target.resolve()),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        (args.output / (name + "-build.log")).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(result.stderr)
        commands.append(cmd)
        libraries.append(target)
    # Loading the kernel DSO first also resolves installations whose HIP SONAME
    # is reachable through its RUNPATH but absent from the system ldconfig cache.
    lib = C.CDLL(str(libraries[0].resolve()))
    runtime = C.util.find_library("amdhip64")
    if not runtime:
        runtime = (
            "/opt/rocm/lib/libamdhip64.so"
            if Path("/opt/rocm/lib/libamdhip64.so").exists()
            else "libamdhip64.so"
        )
    hip = C.CDLL(runtime)
    hip.hipGetErrorString.argtypes = [C.c_int]
    hip.hipGetErrorString.restype = C.c_char_p
    hip.hipMalloc.argtypes = [C.POINTER(C.c_void_p), C.c_size_t]
    hip.hipMemcpy.argtypes = [C.c_void_p, C.c_void_p, C.c_size_t, C.c_int]
    hip.hipFree.argtypes = [C.c_void_p]
    hip.hipDeviceSynchronize.argtypes = []
    hip.hipDeviceGetName.argtypes = [C.c_char_p, C.c_int, C.c_int]

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
    lib.run_case.argtypes = [C.c_int, C.POINTER(C.c_void_p), C.c_void_p]
    probes = C.CDLL(str(libraries[1].resolve()))
    probes.probe.argtypes = [C.c_int, C.c_void_p, C.c_void_p, C.c_void_p, C.c_int]
    report = {
        "schema": 1,
        "experiment": "nonlinear-v2-certified-source-and-hardware-calibration",
        "status": "running",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "device": name.value.decode(),
        "architecture": args.arch,
        "compiler": subprocess.check_output(["hipcc", "--version"], text=True),
        "compile_commands": commands,
        "runner_sha256": sha(Path(__file__)),
        "wrapper_sha256": sha(args.input / "certified.hip"),
        "dataset_sha256": sha(args.input / "cases.json"),
        "certificate_index_sha256": sha(args.certificate_index),
        "probe_sha256": sha(root / "probes.hip"),
        "libraries_sha256": [sha(x) for x in libraries],
        "reference": dataset["reference"],
        "model_calls": 0,
        "cases": [],
        "scope": "Reduced-shape independent kernels, explicit half conversions, abstract scalar operations. No original paper registry, whole IEEE guarantee, or original-size certificate.",
    }

    def save():
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    for i, row in enumerate(dataset["cases"]):
        result = {
            k: row[k]
            for k in (
                "key",
                "dtype",
                "rtol",
                "atol",
                "source_sha256",
                "reference_sha256",
                "task_sha256",
            )
        }
        result.update(certificate=index[row["key"]], trials=[])
        for trial in row["trials"]:
            allocations = []
            payloads = []
            try:
                for b in trial["buffers"]:
                    kind = "e" if b["dtype"] == "float16" else "f"
                    payload = packed(
                        b["values"] if b["role"] == "input" else [float("nan")] * b["size"], kind
                    )
                    allocations.append(upload(payload))
                    payloads.append(payload)
                pointers = (C.c_void_p * len(allocations))(*allocations)
                checked(lib.run_case(i, pointers, None))
                checked(hip.hipDeviceSynchronize())
                errors = []
                for b, device, payload in zip(trial["buffers"], allocations, payloads):
                    actual = download(device, len(payload))
                    if b["role"] == "input":
                        if actual != payload:
                            raise RuntimeError("Input modified: " + row["key"])
                    else:
                        values = unpacked(actual, "e" if b["dtype"] == "float16" else "f")
                        for a, e in zip(values, trial["expected"]):
                            if not math.isfinite(a) or abs(a - e) > row["atol"] + row["rtol"] * abs(
                                e
                            ):
                                raise RuntimeError(
                                    f"{row['key']} trial {trial['trial']}: {a} != {e}"
                                )
                            errors.append(abs(a - e))
                result["trials"].append(
                    {
                        "trial": trial["trial"],
                        "max_abs_error": max(errors),
                        "inputs_unchanged": True,
                    }
                )
            finally:
                for device in allocations:
                    checked(hip.hipFree(device))
        result["status"] = "passed"
        report["cases"].append(result)
        save()
        print(row["key"], "10 GPU checks passed", flush=True)
    data = json.loads(args.calibration.read_text())
    n = len(data["x"])
    allocations = []
    try:
        x = upload(packed(data["x"], "f"))
        allocations.append(x)
        positive = upload(packed(data["positive"], "f"))
        allocations.append(positive)
        out = upload(packed([float("nan")] * (4 * n), "f"))
        allocations.append(out)
        checked(probes.probe(0, x, positive, out, n))
        checked(hip.hipDeviceSynchronize())
        actual = unpacked(download(out, 4 * 4 * n), "f")
        comparisons = []
        for j, op in enumerate(data["ops"]):
            expected = unpacked(packed(data["lean_results"][j], "f"), "f")
            values = actual[j * n : (j + 1) * n]
            mismatch = sum(
                not math.isfinite(a) or abs(a - e) > 1e-6 + 2e-6 * abs(e)
                for a, e in zip(values, expected)
            )
            comparisons.append(
                {
                    "op": op,
                    "comparisons": n,
                    "mismatches": mismatch,
                    "max_abs_error": max(abs(a - e) for a, e in zip(values, expected)),
                    "max_relative_error": max(
                        abs(a - e) / max(abs(e), 1e-30) for a, e in zip(values, expected)
                    ),
                }
            )
        report["scalar_calibration"] = {
            "rtol": 2e-6,
            "atol": 1e-6,
            "ops": comparisons,
            "operand_sha256": sha(args.calibration),
            "model_sha256": data["model_sha256"],
            "lean_source_sha256": data["lean_source_sha256"],
            "scope": data["scope"],
        }
        save()
        if any(r["mismatches"] for r in comparisons):
            raise RuntimeError("Scalar calibration mismatches")
    finally:
        for device in allocations:
            checked(hip.hipFree(device))
    bits = [i for i in range(65536) if i & 0x7C00 != 0x7C00]
    payload = packed(bits, "H")
    expected = packed(unpacked(payload, "e"), "f")
    allocations = []
    try:
        half = upload(payload)
        allocations.append(half)
        decoded = upload(bytes(4 * len(bits)))
        allocations.append(decoded)
        encoded = upload(bytes(2 * len(bits)))
        allocations.append(encoded)
        checked(probes.probe(1, half, decoded, encoded, len(bits)))
        checked(hip.hipDeviceSynchronize())
        a = download(decoded, len(expected))
        b = download(encoded, len(payload))
        decode_mismatches = sum(a[i : i + 4] != expected[i : i + 4] for i in range(0, len(a), 4))
        roundtrip_mismatches = sum(b[i : i + 2] != payload[i : i + 2] for i in range(0, len(b), 2))
        report["half_decode"] = {
            "finite_encodings": len(bits),
            "decode_mismatches": decode_mismatches,
            "roundtrip_mismatches": roundtrip_mismatches,
            "oracle": "Python struct IEEE binary16/binary32, bitwise equality including signed zero; excludes exponent-31 encodings",
        }
        if decode_mismatches or roundtrip_mismatches:
            raise RuntimeError("Half decoding mismatch")
    finally:
        for device in allocations:
            checked(hip.hipFree(device))
    rng = random.Random(261102028)
    words = [0, 0x80000000]
    while len(words) < 4096:
        value = rng.getrandbits(32)
        if value & 0x7F800000 != 0x7F800000:
            words.append(value)
    for _ in range(512):
        lo = rng.randrange(0x7BFF)
        a, b = unpacked(packed([lo, lo + 1], "H"), "e")
        mid = (a + b) / 2
        word = unpacked(packed([mid], "f"), "I")[0]
        for delta in (-1, 0, 1):
            words.extend([word + delta, (word + delta) | 0x80000000])
    values = unpacked(packed(words, "I"), "f")
    expected_bits = []
    for value in values:
        try:
            expected_bits.append(unpacked(packed([value], "e"), "H")[0])
        except OverflowError:
            expected_bits.append(0xFC00 if value < 0 else 0x7C00)
    allocations = []
    try:
        x = upload(packed(words, "I"))
        allocations.append(x)
        out = upload(bytes(2 * len(words)))
        allocations.append(out)
        checked(probes.probe(2, x, out, None, len(words)))
        checked(hip.hipDeviceSynchronize())
        actual = unpacked(download(out, 2 * len(words)), "H")
        mismatch = sum(a != b for a, b in zip(actual, expected_bits))
        report["half_encode"] = {
            "comparisons": len(words),
            "mismatches": mismatch,
            "seed": 261102028,
            "scope": "Finite random binary32 words plus binary16 midpoint ties and adjacent binary32 values, signed zero, overflow and underflow; Python struct round-to-nearest-even oracle",
        }
        if mismatch:
            raise RuntimeError("Half encoding mismatch")
    finally:
        for device in allocations:
            checked(hip.hipFree(device))
    report["status"] = "passed"
    save()
    print(
        "PASSED",
        len(report["cases"]) * 10,
        "kernel trials;",
        4 * n,
        "scalar comparisons;",
        2 * len(bits) + len(words),
        "conversion comparisons",
        flush=True,
    )


if __name__ == "__main__":
    main()
