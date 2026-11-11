"""Closed development reader for the full native llm.c softmax adaptation.

Private register arrays and a negative-infinity seed are opt-in here. The
pinned scalar/collective machines and ordinary accepted source subset do not
change. There is no complete source certificate for this family yet.
"""

from dataclasses import dataclass, field, replace
import json

from . import collective, partition_collective
from .frontend import Translation as BaseTranslation
from .ir import Buffer, Refusal, Task, node

WIDTH = 50257
BLOCK = 1024
MAX_ROWS = (2 ** 31 - 1) // WIDTH
FUEL = (4096, 8, 5, 1)
# Reserved abstract-operation key; its positive denominator is executable by
# the pinned machine. It has no ordinary rational/real/IEEE interpretation here.
NEG_INF_SEED_DENOMINATOR = 2 ** 32


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

    def declare(self, name, kind, id, constant=False):
        if name == "INFINITY":
            raise Refusal("native-softmax-seed", "INFINITY is a reserved source constant")
        super().declare(name, kind, id, constant)

    def expr(self, mode, precedence=0):
        if (mode == "scalar" and self.peek() == "-" and self.i + 1 < len(self.tokens)
                and self.tokens[self.i + 1].text == "INFINITY"):
            self.pop("-")
            self.pop("INFINITY")
            return node("lit", -1, NEG_INF_SEED_DENOMINATOR)
        return super().expr(mode, precedence)

    def statement(self):
        if (self.peek() == "float" and self.i + 2 < len(self.tokens)
                and self.tokens[self.i + 2].text == "["):
            self.pop("float")
            name = self.name()
            self.pop("[")
            self.pop("8")
            self.pop("]")
            self.pop(";")
            self.declare(name, "local", len(self.locals))
            self.locals.append((name, 8))
        else:
            super().statement()

    def read(self):
        tr = super().read()
        return Translation(tr.entry, tr.tokens, tr.trailing, tr.program, tr.shared,
                           self.locals, self.symbols.copy())


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 2 or [b["name"] for b in buffers] != ["out", "inp"]
            or [b["role"] for b in buffers] != ["output", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-softmax", "FP16 output and read-only input required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 2
            or any(type(n) is not int for n in shape) or not 1 <= shape[0] <= MAX_ROWS
            or shape[1] != WIDTH or buffers[1]["shape"] != shape
            or any(type(n) is not int for n in buffers[1]["shape"])):
        raise Refusal("native-softmax", "contiguous [rows,50257] with positive rows and signed-index span required")
    rows = shape[0]
    if (data["entry"] != "softmax_forward_kernel7" or data.get("language") != "hip"
            or data["launch"] != {"grid": rows, "block": BLOCK, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL) or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-softmax", "block1024/wave64 and pinned fuel required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(checked, grid=rows, block=BLOCK, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))


def translate(source, task):
    if task.language != "hip" or task.block != BLOCK or task.warp != 64 or task.fuel != FUEL:
        raise Refusal("native-softmax", "closed native block1024/wave64 contract required")
    tr = Reader(source, task).read()
    if tr.readback().encode() != source.encode():
        raise Refusal("readback", "native softmax source does not reconstruct byte-for-byte")
    return tr


class Machine(partition_collective.Machine):
    def location(self, t, space, buffer, index, write=False):
        if space == "local":
            offset = self.ix(t, index)
            if not 0 <= offset < self.translation.locals[buffer][1]:
                raise Refusal("bounds", "private register-array index outside 0..7")
            return space, t, buffer, offset
        return super().location(t, space, buffer, index, write)
