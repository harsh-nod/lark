"""Hash-bound FP16/FP32 probes and fixed three-stage attention pointer wiring."""

import hashlib
import json
import math
from pathlib import Path
import struct

STAGES = ("score", "softmax", "value")
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
    score, softmax, value = tasks(row)
    return [
        *score["buffers"][:2],
        value["buffers"][1],
        dict(score["buffers"][2], role="scratch"),
        dict(softmax["buffers"][1], role="scratch"),
        value["buffers"][2],
    ]


def wrapper_source(rows):
    parts = ["#include <hip/hip_runtime.h>\n#include <hip/hip_fp16.h>\n#include <cmath>\n"]
    parts += [row[s + ".cu"] for row in rows for s in STAGES]
    parts.append('extern "C" int run_case(int id,void** a,void* stream) {\n')
    for i, row in enumerate(rows):
        parts.append(f"if(id=={i}) {{\n")
        for t, pointers in zip(tasks(row), ((0, 1, 3), (3, 4), (4, 2, 5))):
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
        parts.append("return 0; }\n")
    return "\n".join(parts) + "return -1; }\n"


def validate_bundle(data, index, wrapper):
    if [r["key"] for r in data["cases"]] != ["dense", "gqa"] or set(index) != {"dense", "gqa"}:
        raise RuntimeError("Expected dense and GQA pipelines")
    for row, dims in zip(data["cases"], ([1, 1, 128, 256], [8, 2, 128, 64])):
        cert = index[row["key"]]
        if (
            cert["status"] != "verified"
            or cert["profile"] != "attention-pipeline-v12"
            or cert["attention_dimensions"] != dims
            or any(type(n) is not int for n in cert["attention_dimensions"])
        ):
            raise RuntimeError("Expected the full-size attention certificate")
        names = tuple(x for s in STAGES for x in (s + ".cu", s + "-task.json")) + ("reference.py",)
        for name in names:
            if hashlib.sha256(row[name].encode()).hexdigest() != cert["source_hashes"][name]:
                raise RuntimeError("Certificate binding differs: " + name)
        hq, hkv, seq, dim = dims
        declared = buffers(row)
        shapes = [
            [hq, seq, dim],
            [hkv, seq, dim],
            [hkv, seq, dim],
            [hq, seq, seq],
            [hq, seq, seq],
            [hq, seq, dim],
        ]
        if [b["shape"] for b in declared] != shapes or [b["dtype"] for b in declared] != [
            "float16"
        ] * 3 + ["float32"] * 2 + ["float16"]:
            raise RuntimeError("Allocation shapes or precision differ")
        s, p, v = tasks(row)
        if s["buffers"][2] != dict(p["buffers"][0], role="output") or p["buffers"][1] != dict(
            v["buffers"][0], role="output"
        ):
            raise RuntimeError("Intermediate wiring differs")
        if (
            row["tolerances"] != TOLERANCES
            or len(row["trials"]) != 10
            or {t["trial"] for t in row["trials"]} != set(range(10))
        ):
            raise RuntimeError("Numerical protocol differs")
        for trial in row["trials"]:
            if len(trial["buffers"]) != 6:
                raise RuntimeError("Expected six allocations")
            for b, e in zip(trial["buffers"], declared):
                size = math.prod(e["shape"])
                if (b["size"], b["dtype"], b["role"]) != (size, e["dtype"], e["role"]):
                    raise RuntimeError("Allocation differs from certified signature")
                vals = b["values"] if b["role"] == "input" else b["expected"]
                if len(vals) != size or not all(math.isfinite(x) for x in vals):
                    raise RuntimeError("Invalid scalar probes")
    if (
        wrapper != wrapper_source(data["cases"])
        or hashlib.sha256(wrapper.encode()).hexdigest() != data["wrapper_sha256"]
    ):
        raise RuntimeError("Wrapper differs from sources/order/pointer wiring")
