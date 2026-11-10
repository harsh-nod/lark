"""Hash-bound FP16/FP32 probes and fixed four-stage SwiGLU pointer wiring."""

import hashlib
import json
import math
from pathlib import Path
import struct

STAGES = ("gate", "up", "combine", "down")
TOLERANCES = {"float16": {"rtol": 0.01, "atol": 0.01}, "float32": {"rtol": 2e-5, "atol": 2e-6}}


class PackedValues:
    def __init__(self, payload, dtype):
        self.payload = payload
        self.format = {"float16": "e", "float32": "f"}[dtype]
        self.stride = struct.calcsize("<" + self.format)
        if len(payload) % self.stride:
            raise RuntimeError("Incomplete scalar payload")

    def __len__(self):
        return len(self.payload) // self.stride

    def __iter__(self):
        return (x[0] for x in struct.iter_unpack("<" + self.format, self.payload))


def load_dataset(root):
    root = Path(root)
    data = json.loads((root / "cases.json").read_text())
    raw = (root / "tensors.bin").read_bytes()
    if hashlib.sha256(raw).hexdigest() != data["tensor_data_sha256"]:
        raise RuntimeError("Binary probe file differs")
    view = memoryview(raw)

    def values(record, dtype):
        start, size = record["offset"], record["bytes"]
        if (
            type(start) is not int
            or type(size) is not int
            or min(start, size) < 0
            or start + size > len(view)
        ):
            raise RuntimeError("Invalid probe extent")
        part = view[start : start + size]
        if hashlib.sha256(part).hexdigest() != record["sha256"]:
            raise RuntimeError("Probe extent differs")
        return PackedValues(part, dtype)

    for row in data["cases"]:
        for trial in row["trials"]:
            for b in trial["buffers"]:
                if b["role"] == "input":
                    b["values"] = values(b["packed"], b["dtype"])
                else:
                    b["expected"] = values(b["expected_packed"], b["dtype"])
    return data


def tasks(row):
    return [json.loads(row[s + "-task.json"]) for s in STAGES]


def buffers(row):
    g, u, c, d = tasks(row)
    return [
        *g["buffers"][:2],
        u["buffers"][1],
        d["buffers"][1],
        *(dict(t["buffers"][2], role="scratch") for t in (g, u, c)),
        d["buffers"][2],
    ]


def wrapper_source(row):
    parts = ["#include <hip/hip_runtime.h>\n#include <hip/hip_fp16.h>\n#include <cmath>\n"]
    parts += [row[s + ".cu"] for s in STAGES]
    parts.append('extern "C" int run_case(int id,void** a,void* stream) {\nif(id!=0)return -1;\n')
    for t, pointers in zip(tasks(row), ((0, 1, 4), (0, 2, 5), (4, 5, 6), (6, 3, 7))):
        args = ",".join(
            f"({'const ' if b['role'] == 'input' else ''}{'__half' if b['dtype'] == 'float16' else 'float'}*)a[{p}]"
            for b, p in zip(t["buffers"], pointers)
        )
        parts.append(
            f"hipLaunchKernelGGL({t['entry']},dim3({t['launch']['grid']}),dim3(1),0,(hipStream_t)stream,{args});\n"
        )
        parts.append(
            "{auto e=hipGetLastError();if(e!=hipSuccess)return int(e);e=hipDeviceSynchronize();if(e!=hipSuccess)return int(e);}\n"
        )
    return "\n".join(parts) + "return 0; }\n"


def validate_bundle(data, index, wrapper):
    if len(data["cases"]) != 1 or set(index) != {"swiglu"}:
        raise RuntimeError("Expected exactly one SwiGLU pipeline")
    row = data["cases"][0]
    cert = index["swiglu"]
    if (
        row["key"] != "swiglu"
        or cert["status"] != "verified"
        or cert["profile"] != "swiglu-pipeline-v11"
        or cert["swiglu_dimensions"] != [64, 256, 1024, 256]
        or any(type(n) is not int for n in cert["swiglu_dimensions"])
    ):
        raise RuntimeError("Expected the full-size SwiGLU certificate")
    names = tuple(x for s in STAGES for x in (s + ".cu", s + "-task.json")) + ("reference.py",)
    for name in names:
        if hashlib.sha256(row[name].encode()).hexdigest() != cert["source_hashes"][name]:
            raise RuntimeError("Certificate binding differs: " + name)
    declared = buffers(row)
    shapes = [
        [64, 256],
        [256, 1024],
        [256, 1024],
        [1024, 256],
        [64, 1024],
        [64, 1024],
        [64, 1024],
        [64, 256],
    ]
    if [b["shape"] for b in declared] != shapes:
        raise RuntimeError("Expected full-size SwiGLU allocations")
    if [b["dtype"] for b in declared] != ["float16"] * 4 + [
        "float32",
        "float32",
        "float16",
        "float16",
    ]:
        raise RuntimeError("Projection precision differs")
    g, u, c, d = tasks(row)
    if (
        g["buffers"][0] != u["buffers"][0]
        or g["buffers"][2] != dict(c["buffers"][0], role="output")
        or u["buffers"][2] != dict(c["buffers"][1], role="output")
        or c["buffers"][2] != dict(d["buffers"][0], role="output")
    ):
        raise RuntimeError("Intermediate wiring differs")
    if (
        row["tolerances"] != TOLERANCES
        or len(row["trials"]) != 10
        or {t["trial"] for t in row["trials"]} != set(range(10))
    ):
        raise RuntimeError("Numerical protocol differs")
    for trial in row["trials"]:
        if len(trial["buffers"]) != 8:
            raise RuntimeError("Expected eight allocations")
        for b, e in zip(trial["buffers"], declared):
            size = math.prod(e["shape"])
            if (b["size"], b["dtype"], b["role"]) != (size, e["dtype"], e["role"]):
                raise RuntimeError("Allocation differs from certified signature")
            vals = b["values"] if b["role"] == "input" else b["expected"]
            if len(vals) != size or not all(math.isfinite(x) for x in vals):
                raise RuntimeError("Invalid scalar probes")
    if (
        wrapper != wrapper_source(row)
        or hashlib.sha256(wrapper.encode()).hexdigest() != data["wrapper_sha256"]
    ):
        raise RuntimeError("Wrapper differs from sources/order/pointer wiring")
