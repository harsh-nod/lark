"""Closed development reader for SGLang's packed double-load RMSNorm path.

Private half arrays retain the preloaded input/weight and converted outputs.
The original shared stores and an explicitly guarded repair remain distinct.
Parsing and finite Python execution do not issue a source certificate.
"""

import ast
from dataclasses import dataclass, field, replace
import json

from . import collective, partition_collective
from .frontend import Translation as BaseTranslation
from .ir import Buffer, Refusal, Task, node

WIDTH = 16384
MAX_ROWS = 131072
FUEL = (512, 8, 3, 1)


@dataclass
class Translation(BaseTranslation):
    locals: list[tuple[str, int]] = field(default_factory=list)
    symbols: dict = field(default_factory=dict)

    def data(self):
        return {**super().data(), "locals": self.locals, "symbols": self.symbols}


class Reader(collective.Reader):
    memory_spaces = frozenset({"global", "shared", "local"})

    def __init__(self, source, task):
        super().__init__(source, task)
        self.locals = []

    def statement(self):
        if (self.peek() == "__half" and self.i + 2 < len(self.tokens)
                and self.tokens[self.i + 2].text == "["):
            self.pop("__half")
            name = self.name()
            self.pop("[")
            self.pop("16")
            self.pop("]")
            self.pop(";")
            self.declare(name, "local", len(self.locals))
            self.locals.append((name, 16))
        else:
            super().statement()

    def scalar_type(self, value):
        if value.op == "load" and value.args[0] == "local":
            return "float16"
        return super().scalar_type(value)

    def read(self):
        # The ordinary reader permits only FP32 shared/local storage. This
        # opt-in header and type pass additionally retains typed half caches.
        if self.accept("extern"):
            self.pop('"C"')
        self.pop("__global__")
        self.pop("void")
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("entry", "expected " + self.task.entry)
        self.pop("(")
        for id, buffer in enumerate(self.task.buffers):
            if id:
                self.pop(",")
            constant = self.accept("const")
            self.pop("__half")
            self.pop("*")
            name = self.name()
            if name != buffer.name:
                raise Refusal("signature", "expected buffer " + buffer.name)
            self.declare(name, "global", id, constant)
        self.pop(")")
        self.body()
        if self.peek() != "<eof>":
            raise Refusal("syntax", "exactly one kernel is required")
        self.code.append(node("halt"))
        for instruction in self.code:
            if instruction.op == "set":
                expected, value = "float32", instruction.args[1]
            elif instruction.op == "store":
                space, buffer, _, value = instruction.args
                expected = (self.task.buffers[buffer].dtype if space == "global"
                            else "float16" if space == "local" else "float32")
            else:
                continue
            if self.scalar_type(value) != expected:
                raise Refusal("type", "assignment requires " + expected + "; explicit conversion required")
        return Translation(entry, self.tokens, self.trailing, self.code, self.shared,
                           self.locals, self.symbols.copy())


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 3
            or [b["name"] for b in buffers] != ["output", "input", "weight"]
            or [b["role"] for b in buffers] != ["output", "input", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-sglang-rmsnorm", "FP16 output, read-only input and weight required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 2
            or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= MAX_ROWS or shape[1] != WIDTH
            or buffers[1]["shape"] != shape
            or any(type(n) is not int for n in buffers[1]["shape"])
            or buffers[2]["shape"] != [WIDTH]
            or any(type(n) is not int for n in buffers[2]["shape"])):
        raise Refusal("native-sglang-rmsnorm", "contiguous [rows,16384], rows1..131072 and weight[16384] required")
    rows = shape[0]
    if (data["entry"] != "sglang_rmsnorm" or data.get("language") != "hip"
            or data["launch"] != {"grid": rows, "block": 1024, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL)
            or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-sglang-rmsnorm", "native block1024/wave64 and fixed fuel required")
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
    if task.language != "hip" or task.block != 1024 or task.warp != 64 or task.fuel != FUEL:
        raise Refusal("native-sglang-rmsnorm", "closed native block1024/wave64 contract required")
    tr = Reader(source, task).read()
    if tr.readback() != source:
        raise Refusal("readback", "SGLang source does not reconstruct byte for byte")
    if [n for _, n in tr.locals] != [16, 16, 16] or [n for _, n in tr.shared] != [32]:
        raise Refusal("native-sglang-rmsnorm", "three private half[16] caches and shared float[32] required")
    return tr


def canonical_reference():
    return """import torch


def reference(input, weight):
    x = input.float()
    return (x * torch.rsqrt((x * x).mean(dim=1, keepdim=True) + 1e-5) * weight.float()).half()
"""


def check_reference(source):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference())):
        raise Refusal("native-sglang-rmsnorm-reference", "closed weighted RMSNorm reference required")


class Machine(partition_collective.Machine):
    def location(self, t, space, buffer, index, write=False):
        if space == "local":
            offset = self.ix(t, index)
            if not 0 <= offset < self.translation.locals[buffer][1]:
                raise Refusal("bounds", "private half-cache index outside 0..15")
            return space, t, buffer, offset
        return super().location(t, space, buffer, index, write)
