"""Source-bound native wrapper construction; usable without PyTorch or Lean."""

import hashlib
import json
import math


def wrapper_source(rows):
    wrapper = "#include <hip/hip_runtime.h>\n#include <hip/hip_fp16.h>\n#include <cmath>\n"
    wrapper += "".join(r["source_text"] + "\n" for r in rows)
    wrapper += 'extern "C" int run_case(int id,void** a,void* stream) {\n switch(id) {\n'
    for i, row in enumerate(rows):
        t = json.loads(row["task_text"])
        params = ", ".join(
            f"({'const ' if b['role'] == 'input' else ''}{'__half' if b['dtype'] == 'float16' else 'float'}*)a[{j}]"
            for j, b in enumerate(t["buffers"])
        )
        wrapper += f"case {i}: hipLaunchKernelGGL({t['entry']},dim3({t['launch']['grid']}),dim3({t['launch']['block']}),0,(hipStream_t)stream,{params});break;\n"
    return wrapper + "default:return -1; }return int(hipGetLastError());}\n"


def validate_bundle(dataset, index, wrapper):
    keys = [r["key"] for r in dataset["cases"]]
    if len(set(keys)) != len(keys) or set(keys) != set(index):
        raise RuntimeError("Bundle/certificate case sets differ")
    for row in dataset["cases"]:
        cert = index[row["key"]]
        if cert["status"] != "verified":
            raise RuntimeError("Unverified program: " + row["key"])
        for name in ("source", "reference", "task"):
            key = name + "_sha256"
            actual = hashlib.sha256(row[name + "_text"].encode("utf-8")).hexdigest()
            if actual != cert[key] or row[key] != cert[key]:
                raise RuntimeError("Certificate binding mismatch: " + row["key"] + " " + name)
        task = json.loads(row["task_text"])
        expected_tolerance = (0.01, 0.01) if row["dtype"] == "float16" else (2e-5, 2e-6)
        if (row["rtol"], row["atol"]) != expected_tolerance:
            raise RuntimeError("Numerical tolerance differs from the protocol")
        if len(row["trials"]) != 10 or {t["trial"] for t in row["trials"]} != set(range(10)):
            raise RuntimeError("Trial set differs from the protocol")
        if any(b["dtype"] != row["dtype"] for b in task["buffers"]):
            raise RuntimeError("Mixed or inconsistent data dtype")
        for trial in row["trials"]:
            if len(trial["buffers"]) != len(task["buffers"]):
                raise RuntimeError("Buffer count differs")
            for b, declared in zip(trial["buffers"], task["buffers"]):
                size = math.prod(declared["shape"])
                if (b["role"], b["dtype"], b["size"]) != (
                    declared["role"],
                    declared["dtype"],
                    size,
                ):
                    raise RuntimeError("Host allocation differs from certified task")
                if b["role"] == "input" and len(b["values"]) != size:
                    raise RuntimeError("Input length differs from allocation")
                if b["role"] == "input" and not all(math.isfinite(v) for v in b["values"]):
                    raise RuntimeError("Nonfinite numerical input")
            if len(trial["expected"]) != sum(
                math.prod(b["shape"]) for b in task["buffers"] if b["role"] == "output"
            ):
                raise RuntimeError("Expected output footprint differs")
            if not all(math.isfinite(v) for v in trial["expected"]):
                raise RuntimeError("Nonfinite expected output")
    if wrapper != wrapper_source(dataset["cases"]):
        raise RuntimeError("Wrapper differs from certified source/task bytes")
    if hashlib.sha256(wrapper.encode()).hexdigest() != dataset["wrapper_sha256"]:
        raise RuntimeError("Wrapper hash differs")
