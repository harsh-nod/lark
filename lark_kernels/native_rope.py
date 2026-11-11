"""Native vLLM RoPE development interface, with seeded query/key buffers.

This reader is a source-binding and finite-execution tool. A complete native
launch/reference certificate is not issued by this module.
"""

import ast
from dataclasses import dataclass, replace
import json

from . import collective
from .ir import Buffer, Refusal, Task, node

FUEL = (256, 1, 1, 1)
LAYOUTS = ("interleaved", "split-half")


@dataclass(frozen=True)
class Contract:
    task: Task
    rotary_layout: str
    inout: tuple[int, ...] = (0, 1)


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 3
            or [b["name"] for b in buffers] != ["query", "key", "cache"]
            or [b["role"] for b in buffers] != ["inout", "inout", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-rope", "FP16 query/key in-out and read-only cache required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 3
            or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= 65535 or shape[1:] != [32, 128]
            or buffers[1]["shape"] != [shape[0], 8, 128]
            or buffers[2]["shape"] != [shape[0], 128]
            or any(type(n) is not int for b in buffers[1:] for n in b["shape"])):
        raise Refusal("native-rope", "contiguous Q[tokens,32,128], K[tokens,8,128], cache[tokens,128] required")
    rows = shape[0]
    layout = data.get("rotary_layout")
    if (layout not in LAYOUTS or data["entry"] != "rotary_embedding"
            or data.get("language") != "hip"
            or data["launch"] != {"grid": rows, "block": 512, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL)
            or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-rope", "closed layout, native block512/wave64 and pinned fuel required")
    proxy = json.loads(source)
    del proxy["rotary_layout"]
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
        if b["role"] == "inout":
            b["role"] = "output"
    checked = Task.parse(json.dumps(proxy))
    task = replace(checked, grid=rows, block=512, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))
    return Contract(task, layout)


def translate(source, contract):
    if contract.inout != (0, 1) or contract.rotary_layout not in LAYOUTS:
        raise Refusal("native-rope", "closed initialized query/key interface required")
    tr = collective.Reader(source, contract.task).read()
    if tr.readback() != source:
        raise Refusal("readback", "source does not reconstruct byte for byte")
    return tr


def canonical_reference(layout):
    if layout not in LAYOUTS:
        raise Refusal("native-rope", "unknown rotary layout")
    split = ("x = values[..., :64].float()\n    y = values[..., 64:].float()"
             if layout == "split-half" else
             "x = values[..., 0::2].float()\n    y = values[..., 1::2].float()")
    join = ("torch.cat((ox, oy), dim=-1)" if layout == "split-half" else
            "torch.stack((ox, oy), dim=-1).flatten(-2)")
    return f'''import torch


def rotate(values, cache):
    {split}
    c = cache[:, None, :64].float()
    s = cache[:, None, 64:].float()
    ox = (x * c - y * s).half()
    oy = (y * c + x * s).half()
    return {join}


def reference(query, key, cache):
    return rotate(query, cache), rotate(key, cache)
'''


def check_reference(source, layout):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference(layout))):
        raise Refusal("native-rope-reference", "closed two-output rotary reference required")


def pair_of_column(col, layout):
    if layout == "interleaved":
        return col // 128 * 64 + col % 128 // 2
    if layout == "split-half":
        return col // 128 * 64 + col % 64
    raise Refusal("native-rope", "unknown rotary layout")


class Machine(collective.Machine):
    def __init__(self, contract, translation):
        super().__init__(contract.task, translation)
        self.contract = contract
        for b in contract.inout:
            for i in range(self.task.buffers[b].size):
                self.memory[("global", 0, b, i)] = node("input", b, i)


class AccessPreflight(Machine):
    """Complete finite trace classification; symbolic values stay intact."""

    def access(self, t, loc, write):
        space, owner, buffer, offset = loc
        if space != "global" or owner != 0:
            raise Refusal("native-rope-footprint", "unexpected non-global access")
        if buffer == 2:
            good = not write and offset // 128 == t // 512
        else:
            width = (4096, 1024)[buffer]
            row, col = divmod(offset, width)
            writer = row * 512 + pair_of_column(col, self.contract.rotary_layout) % 512
            good = buffer in self.contract.inout and t == writer
        if not good:
            raise Refusal("native-rope-footprint", f"unexpected access {t,loc,write}")
        super().access(t, loc, write)
