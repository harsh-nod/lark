"""Closed contract for the native weighted 16,384-column RMSNorm profile.

The explicit verify-native-rmsnorm profile checks complete actual-launch proofs.
Parsing this contract alone is not certificate acceptance.
"""

import ast
from dataclasses import replace
import json
import keyword
import re

from .ir import Buffer, Refusal, Task


def canonical_reference(input_name="input", weight_name="weight"):
    occupied = {input_name, weight_name}

    def fresh(preferred):
        while preferred in occupied:
            preferred += "_"
        occupied.add(preferred)
        return preferred

    module = fresh("torch")
    temporary = fresh("x")
    imported = "torch" if module == "torch" else f"torch as {module}"
    return f"""import {imported}


def reference({input_name}, {weight_name}):
    {temporary} = {input_name}.float()
    return ({temporary} * {module}.rsqrt(({temporary} * {temporary}).mean(dim=1, keepdim=True) + 1e-5) * {weight_name}.float()).half()
"""


def check_reference(reference, task):
    wanted = canonical_reference(task.buffers[1].name, task.buffers[2].name)
    if ast.dump(ast.parse(reference)) != ast.dump(ast.parse(wanted)):
        raise Refusal("native-rmsnorm-reference", "closed weighted FP32 RMSNorm reference required")


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if len(buffers) != 3 or [b["role"] for b in buffers] != ["output", "input", "input"]:
        raise Refusal("native-rmsnorm", "output, input and weight buffers required")
    shape = buffers[0]["shape"]
    if (
        not isinstance(shape, list)
        or len(shape) != 2
        or any(type(x) is not int for x in shape)
        or not 1 <= shape[0] < 256
        or shape[1] != 16384
        or buffers[1]["shape"] != shape
        or any(type(x) is not int for x in buffers[1]["shape"])
        or buffers[2]["shape"] != [16384]
        or any(type(x) is not int for x in buffers[2]["shape"])
        or any(b["dtype"] != "float16" for b in buffers)
    ):
        raise Refusal("native-rmsnorm", "contiguous FP16 [rows,16384], 1<=rows<256, weight[16384]")
    rows = shape[0]
    if (
        data.get("language") != "hip"
        or data["launch"] != {"grid": rows, "block": 1024, "warp": 64}
        or any(type(x) is not int for x in data["launch"].values())
    ):
        raise Refusal(
            "native-rmsnorm", "native upstream grid=rows/block1024/wave64 launch required"
        )
    fuel = [256, 8, 3, 1]
    if data.get("fuel") != fuel or any(type(x) is not int for x in data["fuel"]):
        raise Refusal("native-rmsnorm", "development fuel [256,8,3,1] required")
    for b in buffers:
        if (
            not isinstance(b["name"], str)
            or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", b["name"])
            or keyword.iskeyword(b["name"])
        ):
            raise Refusal("native-rmsnorm", "ordinary buffer identifiers required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(
        checked,
        grid=rows,
        block=1024,
        fuel=tuple(fuel),
        buffers=tuple(
            Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
            for b, raw in zip(checked.buffers, buffers)
        ),
    )
