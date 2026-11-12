"""Development-only FP16 AWQ GEMM port with native wave64 matrix instructions.

Retains padded shared staging, both K32 barriers, two K16 matrix passes and
row-tail guards. Parsing/finite execution alone issues no source certificate.
"""

from dataclasses import dataclass, field, replace
from collections import defaultdict
import ast
import json

from . import mfma
from .frontend import Translation as BaseTranslation
from .ir import Buffer, Refusal, Task, node

ENTRY = "awq_fp16_gemm"
LANE_FUEL = 512
MAX_SHARED_HALF_CELLS = 4352  # Exact upstream N128 tile: 32*(128+8).
INT32_SIZE = 2**31


@dataclass(frozen=True)
class Shape:
    m: int
    k: int
    n: int

    def __post_init__(self):
        if (any(type(v) is not int or v <= 0 for v in (self.m, self.k, self.n))
                or self.k % 32 or self.n % 64
                or max(self.m*self.k, self.k*self.n, self.m*self.n) > INT32_SIZE
                or self.grid*64 > INT32_SIZE):
            raise Refusal("native-awq-shape", "positive M, K%32=0, N%64=0 and int32 address bounds required")

    @property
    def tile_n(self):
        return 128 if self.n % 128 == 0 else 64

    @property
    def column_tiles(self):
        return self.n // self.tile_n

    @property
    def grid(self):
        return ((self.m+15)//16)*self.column_tiles

    @property
    def fuel(self):
        # Chosen from the source phase structure before proof attempts. Each
        # K32 has tile_n/8 matrix cuts followed by one scalar closing visit,
        # two block barriers, and the complete launch has one final halt visit.
        return LANE_FUEL, self.tile_n//8+1, 2*(self.k//32)+1, 1


@dataclass
class Translation(BaseTranslation):
    symbols: dict = field(default_factory=dict)

    def data(self):
        return {**super().data(), "shared_dtypes": ["float16"]*len(self.shared),
                "symbols": self.symbols}


def shape_of(task):
    return Shape(task.buffers[0].shape[0], task.buffers[0].shape[1], task.buffers[1].shape[1])


def task_data(shape):
    return {"name": f"native-awq-fp16-M{shape.m}-K{shape.k}-N{shape.n}",
            "entry": ENTRY, "language": "hip", "buffers": [
                {"name": "a", "role": "input", "shape": [shape.m, shape.k], "dtype": "float16"},
                {"name": "b", "role": "input", "shape": [shape.k, shape.n], "dtype": "float16"},
                {"name": "out", "role": "output", "shape": [shape.m, shape.n], "dtype": "float16"}],
            "launch": {"grid": shape.grid, "block": 64, "warp": 64}, "fuel": list(shape.fuel)}


def parse_task(source):
    data = json.loads(source)
    buffers = data["buffers"]
    if (len(buffers) != 3 or [b["name"] for b in buffers] != ["a", "b", "out"]
            or [b["role"] for b in buffers] != ["input", "input", "output"]
            or any(b["dtype"] != "float16" for b in buffers)
            or any(type(b["shape"]) is not list or len(b["shape"]) != 2
                   or any(type(v) is not int for v in b["shape"]) for b in buffers)):
        raise Refusal("native-awq-task", "two contiguous FP16 matrices and one FP16 output required")
    shape = Shape(*buffers[0]["shape"], buffers[1]["shape"][1])
    expected = task_data(shape)
    if (buffers != expected["buffers"] or data.get("entry") != ENTRY or data.get("language") != "hip"
            or data["launch"] != expected["launch"]
            or any(type(v) is not int for v in data["launch"].values())
            or data.get("fuel") != expected["fuel"] or any(type(v) is not int for v in data["fuel"])):
        raise Refusal("native-awq-task", "matrix shapes, native block64 and source-derived fuel required")
    proxy = json.loads(source)
    proxy["launch"] = {"grid": 1, "block": 1, "warp": 64}
    proxy["fuel"] = [4, 1, 1, 1]
    for b in proxy["buffers"]:
        b["shape"] = [1]
    checked = Task.parse(json.dumps(proxy))
    return replace(checked, grid=shape.grid, block=64, warp=64, fuel=shape.fuel,
                   buffers=tuple(Buffer(b.name, b.role, tuple(raw["shape"]), b.dtype)
                                 for b, raw in zip(checked.buffers, buffers)))


class Reader(mfma.Reader):
    """Closed extension for the source's two typed FP16 shared tiles."""

    def scalar_type(self, value):
        if value.op == "load" and value.args[0] == "shared":
            return "float16"
        return super().scalar_type(value)

    def statement(self):
        if self.peek() == "__shared__":
            self.pop("__shared__")
            self.pop("_Float16")
            name = self.name()
            self.pop("[")
            size = self.pop()
            if not size.isdecimal() or not 0 < int(size) <= MAX_SHARED_HALF_CELLS:
                raise Refusal("native-awq-shared", "literal FP16 shared size at most4352 required")
            self.pop("]")
            self.pop(";")
            self.declare(name, "shared", len(self.shared))
            self.shared.append((name, int(size)))
        else:
            super().statement()

    def read(self):
        for name, dtype in (("H4", "_Float16"), ("F4", "float")):
            for token in ("using", name, "=", dtype, "__attribute__", "(", "(",
                          "ext_vector_type", "(", "4", ")", ")", ")", ";"):
                self.pop(token)
        if self.accept("extern"):
            self.pop('\"C\"')
        self.pop("__global__")
        self.pop("void")
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("entry", "expected " + ENTRY)
        self.pop("(")
        for i, buffer in enumerate(self.task.buffers):
            if i:
                self.pop(",")
            constant = self.accept("const")
            self.pop("_Float16")
            self.pop("*")
            name = self.name()
            if name != buffer.name:
                raise Refusal("signature", "expected " + buffer.name)
            self.declare(name, "global", i, constant)
        self.pop(")")
        self.body()
        if self.peek() != "<eof>":
            raise Refusal("syntax", "exactly one native AWQ kernel required")
        self.code.append(node("halt"))
        for instruction in self.code:
            if instruction.op == "set":
                expected, value = self.reg_types.get(instruction.args[0], "float32"), instruction.args[1]
            elif instruction.op == "store":
                expected, value = "float16", instruction.args[3]
            else:
                continue
            if self.scalar_type(value) != expected:
                raise Refusal("native-awq-type", "typed half tiles and explicit output conversion required")
        return Translation(entry, self.tokens, self.trailing, self.code, self.shared, self.symbols.copy())


def translate(source, task):
    shape = shape_of(task)
    if (task.language != "hip" or task.entry != ENTRY or task.grid != shape.grid
            or task.block != 64 or task.warp != 64 or task.fuel != shape.fuel):
        raise Refusal("native-awq-task", "fixed native launch and source-derived fuel required")
    result = Reader(source, task).read()
    if result.readback() != source:
        raise Refusal("readback", "AWQ source does not reconstruct byte for byte")
    if [size for _, size in result.shared] != [640, 32*(shape.tile_n+8)]:
        raise Refusal("native-awq-shared", "padded shared A16x40 and B32x(tile_N+8) required")
    return result


def kernel_source(shape):
    """Emit the independent AMD fragment remapping, retaining upstream staging."""
    m, k, n, tile = shape.m, shape.k, shape.n, shape.tile_n
    banks = tile//16
    lines = ["using H4 = _Float16 __attribute__((ext_vector_type(4)));",
             "using F4 = float __attribute__((ext_vector_type(4)));", "",
             'extern "C" __global__ void awq_fp16_gemm(const _Float16* a, const _Float16* b, _Float16* out) {',
             "  __shared__ _Float16 tileA[640];", f"  __shared__ _Float16 tileB[{32*(tile+8)}];",
             "  int lane = threadIdx.x;", "  int logicalLane = lane % 32;", "  int logicalWarp = lane / 32;",
             "  int block = blockIdx.x;", f"  int blockRow = block / {shape.column_tiles};",
             f"  int blockCol = block % {shape.column_tiles};",
             "  int inputRow = blockRow * 16 + logicalWarp * 8 + logicalLane / 4;",
             "  int inputCol = (logicalLane % 4) * 8;",
             "  int sharedABase = (logicalWarp * 8 + logicalLane / 4) * 40 + inputCol;"]
    for e in range(4):
        lines.append(f"  int outputRow{e} = blockRow * 16 + (lane / 16) * 4 + {e};")
    for bank in range(banks):
        lines.append(f"  F4 acc{bank} = {{0.0f, 0.0f, 0.0f, 0.0f}};")
    lines += ["  int kTile = 0;", f"  while (kTile < {k//32}) {{", "    __syncthreads();",
              "    int ae = 0;", f"    if (inputRow < {m}) {{", "      while (ae < 8) {",
              f"        tileA[sharedABase + ae] = a[inputRow * {k} + kTile * 32 + inputCol + ae];",
              "        ae++;", "      }", "    } else {", "      while (ae < 8) {",
              "        tileA[sharedABase + ae] = __float2half(0.0f);", "        ae++;", "      }", "    }",
              "    int chunk = 0;", f"    while (chunk < {tile//16}) {{",
              f"      int bRow = logicalWarp * {256//tile} + logicalLane / {tile//8} + chunk * {512//tile};",
              f"      int bCol = (logicalLane % {tile//8}) * 8;", "      int be = 0;", "      while (be < 8) {",
              f"        tileB[bRow * {tile+8} + bCol + be] = b[(kTile * 32 + bRow) * {n} + blockCol * {tile} + bCol + be];",
              "        be++;", "      }", "      chunk++;", "    }", "    __syncthreads();"]
    for half in range(2):
        a_values = [f"tileA[(lane % 16) * 40 + {half*16} + (lane / 16) * 4 + {e}]" for e in range(4)]
        lines.append(f"    H4 left{half} = {{{', '.join(a_values)}}};")
        for bank in range(banks):
            b_values = [f"tileB[({half*16} + (lane / 16) * 4 + {e}) * {tile+8} + {bank*16} + lane % 16]" for e in range(4)]
            lines.append(f"    H4 right{half}_{bank} = {{{', '.join(b_values)}}};")
            lines.append(f"    acc{bank} = {mfma.BUILTIN}(left{half}, right{half}_{bank}, acc{bank}, 0, 0, 0);")
    lines += ["    kTile++;", "  }"]
    for bank in range(banks):
        for e in range(4):
            lines += [f"  if (outputRow{e} < {m}) {{",
                      f"    out[outputRow{e} * {n} + blockCol * {tile} + {bank*16} + lane % 16] = __float2half(acc{bank}[{e}]);",
                      "  }"]
    return "\n".join(lines + ["}", ""])


def canonical_reference():
    return "import torch\n\n\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n"


def check_reference(source):
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(canonical_reference())):
        raise Refusal("native-awq-reference", "closed FP16 weighted-matrix reference required")


class Machine(mfma.Machine):
    def race(self):
        # The original scalar check compares every pair of trace entries.
        # Index by location, skip read-only buckets, and retain that same
        # grid/block/warp epoch predicate for all candidate write pairs.
        locations = defaultdict(list)
        for access in self.trace:
            locations[access.location].append(access)
        for accesses in locations.values():
            for a in (event for event in accesses if event.write):
                for b in accesses:
                    if a.thread == b.thread or a.epoch[0] != b.epoch[0]:
                        continue
                    if a.thread//self.task.block == b.thread//self.task.block:
                        if a.epoch[1] != b.epoch[1]:
                            continue
                        if ((a.thread % self.task.block)//self.task.warp
                                == (b.thread % self.task.block)//self.task.warp
                                and a.epoch[2] != b.epoch[2]):
                            continue
                    return a, b
        return None
