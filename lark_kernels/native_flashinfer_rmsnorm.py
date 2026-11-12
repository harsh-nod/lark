"""Development reader for an upstream-derived native FlashInfer RMSNorm.

This closed interface preserves the actual block1024/logical32 reduction and
out-of-place FP16 buffers. Parsing, Python execution and finite access checks
do not issue a certificate or prove complete source correctness.
"""

import ast
from dataclasses import replace
import json

from . import collective
from .ir import Buffer, Refusal, Task

FUEL = (512, 8, 3, 1)
WIDTH = 16384
MAX_ROWS = 131072


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 3
            or [b["name"] for b in buffers] != ["output", "input", "weight"]
            or [b["role"] for b in buffers] != ["output", "input", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-flashinfer-rmsnorm", "FP16 output, input and weight required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 2
            or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= MAX_ROWS or shape[1] != WIDTH
            or buffers[1]["shape"] != shape
            or any(type(n) is not int for n in buffers[1]["shape"])
            or buffers[2]["shape"] != [WIDTH]
            or any(type(n) is not int for n in buffers[2]["shape"])):
        raise Refusal("native-flashinfer-rmsnorm", "contiguous [rows,16384], rows1..131072 and weight[16384] required")
    rows = shape[0]
    if (data["entry"] != "flashinfer_rmsnorm" or data.get("language") != "hip"
            or data["launch"] != {"grid": rows, "block": 1024, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL)
            or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-flashinfer-rmsnorm", "native block1024/wave64 and declared fuel required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(checked, grid=rows, block=1024, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))


def translate(source, task):
    tr = collective.Reader(source, task).read()
    if tr.readback() != source:
        raise Refusal("readback", "source does not reconstruct byte for byte")
    return tr


def canonical_reference():
    return """import torch


def reference(input, weight):
    x = input.float()
    return (x * torch.rsqrt((x * x).mean(dim=1, keepdim=True) + 1e-5) * (0.0 + weight.float())).half()
"""


def check_reference(source):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference())):
        raise Refusal("native-flashinfer-rmsnorm-reference", "closed weighted RMSNorm reference required")
