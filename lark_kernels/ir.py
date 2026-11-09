"""Small, closed data languages; never execute source supplied for verification."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
import math


class Refusal(ValueError):
    def __init__(self, code: str, detail: str):
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@dataclass(frozen=True)
class Node:
    op: str
    args: tuple = ()

    def data(self):
        return [self.op, *[a.data() if isinstance(a, Node) else a for a in self.args]]


def node(op, *args):
    return Node(op, args)


def literal(value: str | int):
    f = Fraction(value)
    return node("lit", f.numerator, f.denominator)


@dataclass(frozen=True)
class Buffer:
    name: str
    role: str
    shape: tuple[int, ...]
    dtype: str = "float32"

    @property
    def size(self):
        return math.prod(self.shape)


@dataclass(frozen=True)
class Task:
    name: str
    entry: str
    language: str
    buffers: tuple[Buffer, ...]
    grid: int
    block: int
    warp: int
    fuel: tuple[int, int, int, int]

    @classmethod
    def read(cls, path):
        return cls.parse(path.read_text())

    @classmethod
    def parse(cls, source):
        d = json.loads(source)
        allowed = {"name", "entry", "language", "buffers", "launch", "fuel"}
        if set(d) - allowed:
            raise Refusal("signature", "unknown task fields")
        bufs = []
        for b in d["buffers"]:
            if set(b) != {"name", "role", "shape", "dtype"} or b["dtype"] not in {
                "float32",
                "float16",
            }:
                raise Refusal(
                    "dtype", "only named, contiguous float32/float16 buffers are supported"
                )
            shape = tuple(b["shape"])
            if not shape or any(type(x) is not int or x <= 0 for x in shape):
                raise Refusal("shape", "dimensions must be positive integers")
            if b["role"] not in {"input", "output", "scratch"}:
                raise Refusal("signature", "role must be input, output, or scratch")
            bufs.append(Buffer(b["name"], b["role"], shape, b["dtype"]))
        if len({b.name for b in bufs}) != len(bufs):
            raise Refusal("signature", "duplicate buffer names")
        launch = d["launch"]
        language = d.get("language", "cuda")
        if language not in {"cuda", "hip"}:
            raise Refusal("language", "implemented frontends: cuda, hip")
        if set(launch) - {"grid", "block", "warp"}:
            raise Refusal("geometry", "only one-dimensional launches are supported")
        grid, block = launch["grid"], launch["block"]
        warp = launch.get("warp", 32 if language == "cuda" else 64)
        if any(type(x) is not int or x <= 0 for x in (grid, block, warp)):
            raise Refusal("geometry", "launch dimensions must be positive integers")
        if warp not in {32, 64} or (language == "cuda" and warp != 32):
            raise Refusal("geometry", "CUDA requires warp=32; HIP supports 32 or 64")
        fuel = tuple(d.get("fuel", [256, 64, 64, 64]))
        if len(fuel) != 4 or any(type(x) is not int or x <= 0 for x in fuel):
            raise Refusal("fuel", "expected four positive lane/warp/block/grid bounds")
        if grid * block > 256 or any(b.size > 4096 for b in bufs):
            raise Refusal(
                "capacity", "bounded certificate profile: <=256 threads, <=4096 cells/buffer"
            )
        if not any(b.role == "output" for b in bufs):
            raise Refusal("signature", "at least one output is required")
        return cls(d["name"], d["entry"], language, tuple(bufs), grid, block, warp, fuel)


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def lean_node(n: Node) -> str:
    op, a = n.op, n.args
    if op == "lit":
        return f"(.lit ({a[0]}) {a[1]})"
    if op in {"const", "ivar", "reg"}:
        return f"(.{op} ({a[0]}))"
    if op in {"tid", "bid", "bdim"}:
        return f".{op}"
    if op == "idx":
        return f"(.index {a[0]} {lean_node(a[1])})"
    if op in {"add", "sub", "mul", "div", "mod", "lt", "le", "eq", "ne"}:
        return f"(.{op} {lean_node(a[0])} {lean_node(a[1])})"
    if op == "bin":
        return f"(.bin .{a[0]} {lean_node(a[1])} {lean_node(a[2])})"
    if op == "un":
        return f"(.un .{a[0]} {lean_node(a[1])})"
    if op == "load":
        return f"(.load .{a[0]} {a[1]} {lean_node(a[2])})"
    if op == "set":
        return f"(.assign {a[0]} {lean_node(a[1])})"
    if op == "store":
        return f"(.store .{a[0]} {a[1]} {lean_node(a[2])} {lean_node(a[3])})"
    if op == "branch":
        return f"(.branch {lean_node(a[0])} {a[1]})"
    if op == "jump":
        return f"(.jump {a[0]})"
    if op == "barrier":
        return f"(.barrier .{a[0]})"
    if op == "halt":
        return ".halt"
    if op == "input":
        return f"(input {a[0]} {a[1]})"
    raise Refusal("internal", f"no Lean emitter for {op}")


def lean_spec(n: Node) -> str:
    if n.op == "input":
        return f"(input {n.args[0]} {n.args[1]})"
    if n.op == "lit":
        return f"(ops.literal ({n.args[0]}) {n.args[1]})"
    if n.op == "bin":
        op, a, b = n.args
        return f"(ops.{op} {lean_spec(a)} {lean_spec(b)})"
    if n.op == "un":
        return f"(ops.{n.args[0]} {lean_spec(n.args[1])})"
    raise Refusal("specification", f"unsupported scalar node {n.op}")
