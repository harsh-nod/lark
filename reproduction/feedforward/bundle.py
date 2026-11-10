"""Fixed two-launch wiring and source/probe validation for the FFN device study."""

import hashlib
import json
import math


def wrapper_source(row):
    up, down = [json.loads(row[k + "-task.json"]) for k in ("up", "down")]
    parts = [
        "#include <hip/hip_runtime.h>\n#include <hip/hip_fp16.h>\n#include <cmath>\n",
        row["up.cu"],
        row["down.cu"],
    ]
    parts.append('extern "C" int run_case(int id,void** a,void* stream) {\nif(id!=0)return -1;\n')
    for task, pointers in ((up, (0, 1, 3)), (down, (3, 2, 4))):
        args = ",".join(
            f"({'const ' if i < 2 else ''}__half*)a[{p}]" for i, p in enumerate(pointers)
        )
        parts.append(
            f"hipLaunchKernelGGL({task['entry']},dim3({task['launch']['grid']}),dim3(1),0,(hipStream_t)stream,{args});\n"
        )
        parts.append(
            "{auto e=hipGetLastError();if(e!=hipSuccess)return int(e);e=hipDeviceSynchronize();if(e!=hipSuccess)return int(e);}\n"
        )
    return "\n".join(parts) + "return 0; }\n"


def buffers(row):
    up, down = [json.loads(row[k + "-task.json"]) for k in ("up", "down")]
    return [
        *up["buffers"][:2],
        down["buffers"][1],
        dict(up["buffers"][2], role="scratch"),
        down["buffers"][2],
    ]


def validate_bundle(data, index, wrapper):
    if len(data["cases"]) != 1 or set(index) != {"ffn"}:
        raise RuntimeError("Expected exactly the FFN pipeline")
    row = data["cases"][0]
    cert = index["ffn"]
    if (
        row["key"] != "ffn"
        or cert["status"] != "verified"
        or cert["profile"] != "feedforward-pipeline-v10"
        or cert["ffn_dimensions"] != [64, 256, 1024, 256]
    ):
        raise RuntimeError("Expected the full-size FFN certificate")
    for name in ("up.cu", "down.cu", "up-task.json", "down-task.json", "reference.py"):
        if hashlib.sha256(row[name].encode()).hexdigest() != cert["source_hashes"][name]:
            raise RuntimeError("Pipeline certificate binding differs: " + name)
    declared = buffers(row)
    if [b["shape"] for b in declared] != [
        [64, 256],
        [256, 1024],
        [1024, 256],
        [64, 1024],
        [64, 256],
    ]:
        raise RuntimeError("Expected full-size FFN buffers")
    up, down = [json.loads(row[k + "-task.json"]) for k in ("up", "down")]
    if up["buffers"][2] != dict(down["buffers"][0], role="output"):
        raise RuntimeError("Intermediate buffers differ")
    if row["dtype"] != "float16" or (row["rtol"], row["atol"]) != (0.01, 0.01):
        raise RuntimeError("Numerical protocol differs")
    if len(row["trials"]) != 10 or {t["trial"] for t in row["trials"]} != set(range(10)):
        raise RuntimeError("Expected ten trials")
    for trial in row["trials"]:
        if len(trial["buffers"]) != 5:
            raise RuntimeError("Expected five allocations")
        for b, expected in zip(trial["buffers"], declared):
            size = math.prod(expected["shape"])
            if (b["size"], b["dtype"], b["role"]) != (size, expected["dtype"], expected["role"]):
                raise RuntimeError("Allocation differs from pipeline contract")
            if b["role"] == "input" and (
                len(b["values"]) != size or not all(math.isfinite(x) for x in b["values"])
            ):
                raise RuntimeError("Invalid numerical input")
        if len(trial["expected"]) != 81920 or not all(math.isfinite(x) for x in trial["expected"]):
            raise RuntimeError("Invalid intermediate/final expected values")
    if (
        wrapper != wrapper_source(row)
        or hashlib.sha256(wrapper.encode()).hexdigest() != data["wrapper_sha256"]
    ):
        raise RuntimeError(
            "Wrapper differs from certified sources, launch order or intermediate wiring"
        )
