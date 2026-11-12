"""Closed native fused Q/K RMSNorm + RoPE source and finite-execution profile.

The separate native_qknorm_rope_certificate backend binds complete interleaved
exact-real launch proofs. Split-half remains a development execution profile.
"""

import ast
from dataclasses import dataclass, replace
import json

from . import collective, partition_collective
from .ir import Buffer, Refusal, Task, node

FUEL = (256, 16, 1, 1)
LAYOUTS = ("interleaved", "split-half")


@dataclass(frozen=True)
class Contract:
    task: Task
    rows: int
    rotary_layout: str


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    names = ["output", "qkv", "q_weight", "k_weight", "cache"]
    if (len(buffers) != 5 or [b["name"] for b in buffers] != names
            or [b["role"] for b in buffers] != ["output", "input", "input", "input", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-qknorm-rope", "separate FP16 output, QKV input, Q/K weights and gathered cache required")
    shape = buffers[0]["shape"]
    if (type(shape) is not list or len(shape) != 3 or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= 65535 or shape[1:] != [40, 128]):
        raise Refusal("native-qknorm-rope", "output[tokens,40,128], tokens1..65535 required")
    rows = shape[0]
    shapes = [[rows, 40, 128], [rows, 48, 128], [128], [128], [rows, 128]]
    if any(b["shape"] != expected or any(type(n) is not int for n in b["shape"])
           for b, expected in zip(buffers, shapes)):
        raise Refusal("native-qknorm-rope", "fixed Q32/K8/V8 heads, width128, Q/K weight128 and gathered cache128 required")
    layout = data.get("rotary_layout")
    if (layout not in LAYOUTS or data["entry"] != "fused_qknorm_rope" or data.get("language") != "hip"
            or data["launch"] != {"grid": rows * 5, "block": 256, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL) or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-qknorm-rope", "closed layout, grid5*tokens, native block256/wave64 and pinned fuel required")
    proxy = json.loads(source)
    del proxy["rotary_layout"]
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    task = replace(checked, grid=rows * 5, block=256, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))
    return Contract(task, rows, layout)


class Reader(collective.Reader):
    def statement(self):
        if self.peek() == "__syncwarp":
            # This closed profile has complete adjacent logical32 heads in
            # every physical wave64, with no padding or partial token block.
            self.pop()
            self.pop("(")
            self.pop(")")
            self.pop(";")
            self.code.append(node("barrier", "warp"))
        else:
            super().statement()


def translate(source, contract):
    result = Reader(source, contract.task).read()
    if result.readback() != source:
        raise Refusal("readback", "native fused Q/K source does not reconstruct byte for byte")
    return result


def canonical_reference(layout):
    if layout not in LAYOUTS:
        raise Refusal("native-qknorm-rope", "unknown rotary layout")
    split = ("x = values[..., :64]\n    y = values[..., 64:]" if layout == "split-half" else
             "x = values[..., 0::2]\n    y = values[..., 1::2]")
    real = "x * c + (-y) * s" if layout == "split-half" else "x * c - y * s"
    imaginary = "y * c + x * s" if layout == "split-half" else "x * s + y * c"
    join = "torch.cat((ox, oy), dim=-1)" if layout == "split-half" else "torch.stack((ox, oy), dim=-1).flatten(-2)"
    return f'''import torch


def normalize(values, weight):
    x = values.float()
    scale = torch.rsqrt((x * x).mean(dim=-1, keepdim=True) + 1e-5)
    return x * (scale * weight.float())


def rotate(values, cache):
    {split}
    c = cache[:, None, :64].float()
    s = cache[:, None, 64:].float()
    ox = {real}
    oy = {imaginary}
    return {join}.half()


def reference(qkv, q_weight, k_weight, cache):
    q = rotate(normalize(qkv[:, :32, :], q_weight), cache)
    k = rotate(normalize(qkv[:, 32:40, :], k_weight), cache)
    return torch.cat((q, k), dim=1)
'''


def check_reference(source, layout):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference(layout))):
        raise Refusal("native-qknorm-rope-reference", "closed fused normalization/rotation reference required")


class AccessPreflight(partition_collective.Machine):
    """Finite actual-access ownership check; scalar expressions stay intact."""

    def __init__(self, contract, translation):
        super().__init__(contract.task, translation)
        self.contract = contract

    def access(self, t, loc, write):
        space, owner, buffer, offset = loc
        row, head = divmod(t // 32, 40)
        lane = t % 32
        if buffer == 0:
            good = write and offset // 5120 == row and offset % 5120 // 128 == head and offset % 128 // 4 == lane
        elif buffer == 1:
            good = not write and offset // 6144 == row and offset % 6144 // 128 == head and offset % 128 // 4 == lane
        elif buffer in (2, 3):
            good = not write and buffer == (2 if head < 32 else 3) and offset // 4 == lane
        elif buffer == 4:
            good = not write and offset // 128 == row
        else:
            good = False
        if space != "global" or owner != 0 or not good:
            raise Refusal("native-qknorm-rope-footprint", f"unexpected access {t,loc,write}")
        super().access(t, loc, write)
