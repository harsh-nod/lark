"""Scoped development contract for initialized, mutable fused RMSNorm buffers.

The existing machine's writable output cells are initialized explicitly from
the in-out interface. This module is not a registered certificate profile.
The ordinary task parser and all pinned earlier machine models are unchanged.
"""

import ast
from dataclasses import dataclass, replace
import json

from . import collective, partition_collective
from .ir import Buffer, Refusal, Task, node

FUEL = (512, 8, 3, 1)


@dataclass(frozen=True)
class Contract:
    task: Task
    inout: tuple[int, ...] = (0, 1)


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 3
            or [b["name"] for b in buffers] != ["input", "residual", "weight"]
            or [b["role"] for b in buffers] != ["inout", "inout", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-fused-rmsnorm", "FP16 input/residual in-out and read-only weight required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 2
            or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= 255 or shape[1] != 16384
            or buffers[1]["shape"] != shape
            or any(type(n) is not int for n in buffers[1]["shape"])
            or buffers[2]["shape"] != [16384]
            or any(type(n) is not int for n in buffers[2]["shape"])):
        raise Refusal("native-fused-rmsnorm", "contiguous [rows,16384], rows1..255, weight[16384] required")
    rows = shape[0]
    if (data["entry"] != "fused_add_rmsnorm" or data.get("language") != "hip"
            or data["launch"] != {"grid": rows, "block": 1024, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL)
            or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-fused-rmsnorm", "native block1024/wave64 and pinned fuel required")
    # Preserve Task.parse's unknown-field, duplicate-name and type checks with a
    # bounded proxy. In-out cells use the existing machine's writable role; their
    # initial values come from the separately declared in-out initializer.
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
        if b["role"] == "inout":
            b["role"] = "output"
    checked = Task.parse(json.dumps(proxy))
    task = replace(checked, grid=rows, block=1024, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))
    return Contract(task)


class Reader(collective.Reader):
    shared_limit = 16384


def translate(source, contract):
    task = contract.task
    if contract.inout != (0, 1) or task.language != "hip" or task.block != 1024 or task.warp != 64:
        raise Refusal("native-fused-rmsnorm", "closed native in-out contract required")
    tr = Reader(source, task).read()
    if tr.readback() != source:
        raise Refusal("readback", "source does not reconstruct byte for byte")
    return tr


def canonical_reference():
    return """import torch


def reference(input, residual, weight):
    x = input.float() + residual.float()
    output = (x * torch.rsqrt((x * x).mean(dim=1, keepdim=True) + 1e-5) * (0.0 + weight.float())).half()
    return output, x.half()
"""


def check_reference(source):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference())):
        raise Refusal("native-fused-rmsnorm-reference", "closed two-output fused reference required")


class Machine(partition_collective.Machine):
    def __init__(self, contract, translation):
        super().__init__(contract.task, translation)
        for b in contract.inout:
            for i in range(self.task.buffers[b].size):
                self.memory[("global", 0, b, i)] = node("input", b, i)


class AccessPreflight(Machine):
    """Finite value-erased source run, not a universal trace or value theorem."""

    def __init__(self, contract, translation):
        super().__init__(contract, translation)
        self.accesses = 0
        self.counts = {}

    def expr(self, t, n):
        op, a = n.op, n.args
        if op in {"lit", "reg"}:
            if op == "reg":
                super().expr(t, n)
            return 0
        if op == "bin":
            self.expr(t, a[1])
            self.expr(t, a[2])
            return 0
        if op == "un":
            self.expr(t, a[1])
            return 0
        super().expr(t, n)
        return 0

    def access(self, t, loc, write):
        space, owner, b, offset = loc
        epoch = self.threads[t].epoch[1]
        if space == "global":
            row, col = divmod(offset, 16384)
            good = (owner == 0 and not write if b == 2 else
                    owner == 0 and t == row * 1024 + (col // 8) % 1024
                    and ((b == 0 and (epoch == 2 if write else epoch == 0))
                         or (b == 1 and epoch == 0)))
        elif space == "shared" and owner == t // 1024:
            lane = t % 1024
            if b == 1:
                good = (offset // 8) % 1024 == lane and epoch == (0 if write else 2)
            else:
                good = ((epoch == 0 and write and lane % 32 == 0 and offset == lane // 32)
                        or (epoch == 1 and not write and lane < 32 and offset == lane)
                        or (epoch == 1 and write and lane == 0 and offset == 0)
                        or (epoch == 2 and not write and offset == 0))
        else:
            good = False
        if not good:
            raise Refusal("native-fused-rmsnorm-footprint", f"unexpected access {t,loc,write,epoch}")
        key = f"{space}:{b}:{'write' if write else 'read'}:epoch{epoch}"
        self.counts[key] = self.counts.get(key, 0) + 1
        self.accesses += 1

    def outputs(self):
        raise Refusal("values-erased", "preflight does not evaluate output values")

    def race(self):
        raise Refusal("trace-erased", "preflight does not retain the actual trace")
