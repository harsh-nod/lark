"""Development reader for the native tiled 128x256 FP16 online-attention source.

This is not a registered certificate profile. It exposes local arrays already
modeled by Lark.Nonlinear without changing the ordinary reader's accepted spaces
or size bounds. Translation and program binding do not prove execution.
"""

import ast
from dataclasses import dataclass, field, replace
import json

from .frontend import Reader, Translation
from .ir import Buffer, Refusal, Task
from .machine import Machine
from .spec import read_spec

FUEL = (1000000, 1, 9, 1)


@dataclass
class NativeTranslation(Translation):
    locals: list[tuple[str, int]] = field(default_factory=list)
    symbols: dict = field(default_factory=dict)

    def data(self):
        return {**super().data(), "locals": self.locals, "symbols": self.symbols}


class NativeReader(Reader):
    memory_spaces = frozenset({"global", "shared", "local"})
    shared_limit = 8192

    def __init__(self, source, task):
        super().__init__(source, task)
        self.locals = []

    def statement(self):
        if (self.peek() == "float" and self.i + 2 < len(self.tokens)
                and self.tokens[self.i + 2].text == "["):
            self.pop("float")
            name = self.name()
            self.pop("[")
            size = self.pop()
            if not size.isdecimal() or not 0 < int(size) <= 4:
                raise Refusal("native-attention-local", "literal private array size in 1..4 required")
            self.pop("]")
            self.pop(";")
            self.declare(name, "local", len(self.locals))
            self.locals.append((name, int(size)))
        else:
            super().statement()

    def read(self):
        tr = super().read()
        return NativeTranslation(tr.entry, tr.tokens, tr.trailing, tr.program, tr.shared,
                                 self.locals, self.symbols.copy())


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 4
            or [b["name"] for b in buffers] != ["out", "query", "key", "value"]
            or [b["role"] for b in buffers] != ["output", "input", "input", "input"]
            or any(b["dtype"] != "float16" for b in buffers)):
        raise Refusal("native-attention", "out/query/key/value FP16 buffers in that order required")
    shape = buffers[0]["shape"]
    if (not isinstance(shape, list) or len(shape) != 3
            or any(type(n) is not int for n in shape)
            or not 1 <= shape[0] <= 65535 or shape[1:] != [128, 256]
            or any(b["shape"] != shape or any(type(n) is not int for n in b["shape"]) for b in buffers)):
        raise Refusal("native-attention", "equal [batchheads,128,256] shapes and span <2^31 required")
    groups = shape[0]
    if (data["entry"] != "online_attention" or data.get("language") != "hip"
            or data["launch"] != {"grid": groups, "block": 32, "warp": 64}
            or any(type(n) is not int for n in data["launch"].values())
            or data.get("fuel") != list(FUEL)
            or any(type(n) is not int for n in data["fuel"])):
        raise Refusal("native-attention", "native 32-thread/wave64 tiled launch and pinned fuel required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(checked, grid=groups, block=32, fuel=FUEL,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))


def translate(source, task):
    if task.language != "hip" or task.block != 32 or task.warp != 64:
        raise Refusal("native-attention", "native 32-thread/wave64 source required")
    tr = NativeReader(source, task).read()
    if tr.readback().encode() != source.encode():
        raise Refusal("readback", "native attention source does not reconstruct byte for byte")
    return tr


def canonical_reference():
    return """import torch


def reference(query, key, value):
    return (((query.float() @ key.float().transpose(1, 2)) / 16.0).softmax(dim=2) @ value.float()).half()
"""


def check_reference(source, task):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference())):
        raise Refusal("native-attention-reference", "closed 128x256 noncausal attention reference required")
    small = replace(task, grid=1, block=1,
                    buffers=tuple(replace(b, shape=(1, 2, 1)) for b in task.buffers))
    read_spec(source, small)


class NativeMachine(Machine):
    """Development preflight with the existing Lean machine's private owner rule."""

    def location(self, t, space, b, ix, write=False):
        if space != "local":
            return super().location(t, space, b, ix, write)
        i = self.ix(t, ix)
        if not 0 <= b < len(self.translation.locals):
            raise Refusal("bounds", "unknown local buffer")
        size = self.translation.locals[b][1]
        if not 0 <= i < size:
            raise Refusal("bounds", f"thread {t}: local buffer {b} offset {i}, size {size}")
        return "local", t, b, i


class AccessPreflight(NativeMachine):
    """Untrusted value-erased run: bounds, initialization, cuts and footprints.

    Scalar values are erased, not numerically evaluated. No data-equivalence or
    universal trace-erasure theorem is asserted. Accesses are checked as they
    happen rather than retained in a many-million-element Python trace.
    """

    def __init__(self, task, translation):
        super().__init__(task, translation)
        self.access_counts = {}
        self.total_accesses = 0
        self.unit = 0

    def expr(self, t, n):
        op, a = n.op, n.args
        if op == "lit":
            return self.unit
        if op == "bin":
            self.expr(t, a[1])
            self.expr(t, a[2])
            return self.unit
        if op == "un":
            self.expr(t, a[1])
            return self.unit
        super().expr(t, n)
        return self.unit

    def outputs(self):
        raise Refusal("values-erased", "access preflight does not evaluate tensor values")

    def race(self):
        raise Refusal("trace-erased", "access preflight does not retain a trace for the pairwise race checker")

    def initialized_output_slots(self):
        return len(super().outputs())

    def access(self, t, loc, write):
        space, owner, b, offset = loc
        epoch = self.threads[t].epoch[1]
        if space == "global":
            good = owner == 0 and (t == offset // 32768 * 32 + offset // 256 % 32 if b == 0 else not write)
        elif space == "local":
            good = owner == t
        elif b in (0, 3):
            good = owner == t // 32 and t % 32 == offset // (256 if b == 0 else 32)
        elif b in (1, 2):
            good = owner == t // 32 and (
                t % 32 == offset // 256 and epoch % 2 == 0 if write else epoch % 2 == 1)
        else:
            good = False
        if not good:
            raise Refusal("native-attention-footprint",
                          f"thread {t}, PC {self.threads[t].pc}, {loc}, write={write}, block epoch={epoch}")
        key = f"{space}:{b}:{'write' if write else 'read'}:block-epoch-{epoch}"
        self.access_counts[key] = self.access_counts.get(key, 0) + 1
        self.total_accesses += 1
