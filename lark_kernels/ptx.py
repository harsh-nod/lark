"""Lossless reader for an explicit, bounded scalar PTX 8.0/sm_80 subset.

The accepted source is not executed. Registers retain run-time initialization,
predicates are materialized, and byte alignment is checked by the Lean machine.
Floating operations use the existing abstract exact-operation interpretation.
This is neither a general PTX implementation nor a NVIDIA execution claim.
"""

from fractions import Fraction
import math
import re
import struct

from .frontend import Token, Translation
from .ir import Refusal, node


TOKEN = re.compile(
    r"(?P<trivia>\s+|//[^\n]*(?:\n|$)|/\*[\s\S]*?\*/)"
    r"|(?P<token>0[fF][0-9a-fA-F]{8}|0[xX][0-9a-fA-F]+|\d+\.\d+|\d+"
    r"|%[A-Za-z_]\w*(?:\.[xyz])?|\.?[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*"
    r"|[{}()[\];,:<>@!+])"
)
REGISTER_TYPES = {".b32", ".u32", ".b64", ".u64", ".f32", ".pred"}


def tokenize(source):
    tokens, leading, pos = [], "", 0
    while pos < len(source):
        match = TOKEN.match(source, pos)
        if not match:
            raise Refusal("ptx-syntax", f"unsupported source at character {pos}")
        if match.lastgroup == "trivia":
            leading += match.group()
        else:
            tokens.append(Token(leading, match.group()))
            leading = ""
        pos = match.end()
    return tokens, leading


class Reader:
    def __init__(self, source, task):
        self.tokens, self.trailing = tokenize(source)
        self.i, self.task = 0, task
        self.code = []
        self.regs, self.values, self.labels = {}, {}, {}
        self.patches = []
        self.nindex = self.nscalar = 0

    def peek(self):
        return self.tokens[self.i].text if self.i < len(self.tokens) else "<eof>"

    def pop(self, expected=None):
        value = self.peek()
        if value == "<eof>" or (expected is not None and value != expected):
            raise Refusal("ptx-syntax", f"token {self.i}: expected {expected}, got {value}")
        self.i += 1
        return value

    def accept(self, value):
        if self.peek() == value:
            self.pop()
            return True
        return False

    def name(self):
        name = self.pop()
        if not re.fullmatch(r"[A-Za-z_]\w*", name):
            raise Refusal("ptx-syntax", "simple identifiers required")
        return name

    def register(self):
        name = self.pop()
        if name not in self.regs:
            raise Refusal("ptx-register", f"undeclared register {name}")
        return name

    def declare(self):
        self.pop(".reg")
        ty = self.pop()
        if ty not in REGISTER_TYPES:
            raise Refusal("ptx-type", "unsupported register type " + ty)
        prefix = self.pop()
        if not re.fullmatch(r"%[A-Za-z_]\w*", prefix):
            raise Refusal("ptx-register", "simple %register names required")
        names = [prefix]
        if self.accept("<"):
            count = self.pop()
            if not count.isdecimal() or not 1 <= int(count) <= 128:
                raise Refusal("ptx-capacity", "register arrays require 1..128 entries")
            self.pop(">")
            names = [prefix + str(i) for i in range(int(count))]
        self.pop(";")
        for name in names:
            if name in self.regs or len(self.regs) >= 256:
                raise Refusal("ptx-register", "duplicate register or >256 declarations")
            self.regs[name] = ty

    def assign(self, dest, kind, expression, buffer=None):
        # Single static assignment prevents a pointer or predicate description
        # from silently referring to an overwritten source register.
        if dest in self.values:
            raise Refusal("ptx-ssa", "register reassignment is outside this PTX subset")
        ty = self.regs[dest]
        allowed = {
            "scalar": {".f32"},
            "index": {".b32", ".u32", ".b64", ".u64"},
            "pointer": {".b64", ".u64"},
            "predicate": {".pred"},
        }[kind]
        if ty not in allowed:
            raise Refusal("ptx-type", f"{dest}: incompatible {ty}/{kind}")
        slot = self.nscalar if kind == "scalar" else self.nindex
        if kind == "scalar":
            self.nscalar += 1
        else:
            self.nindex += 1
        self.values[dest] = (kind, slot, buffer)
        if expression is not None:
            self.code.append(node("set" if kind == "scalar" else "idx", slot, expression))
        return slot

    def value(self, name, kind):
        if name not in self.values or self.values[name][0] != kind:
            raise Refusal("ptx-type", f"{name}: expected initialized {kind} register")
        return self.values[name]

    def integer(self, width=32, *, special=False):
        text = self.pop()
        specials = {"%tid.x": "tid", "%ctaid.x": "bid", "%ntid.x": "bdim"}
        if text in specials:
            if width != 32 or not special:
                raise Refusal("ptx-type", "special registers require mov.u32")
            return node(specials[text])
        if re.fullmatch(r"\d+|0[xX][0-9a-fA-F]+", text):
            value = int(text, 16 if text.lower().startswith("0x") else 10)
            if value >= 2**31:
                raise Refusal("ptx-integer", "only nonnegative int32 values are accepted")
            return node("const", value)
        _, slot, _ = self.value(text, "index")
        if self.regs[text] not in {f".b{width}", f".u{width}"}:
            raise Refusal("ptx-type", "integer operand width differs")
        return node("ivar", slot)

    def scalar(self):
        text = self.pop()
        if re.fullmatch(r"0[fF][0-9a-fA-F]{8}", text):
            value = struct.unpack(">f", bytes.fromhex(text[2:]))[0]
            if not math.isfinite(value):
                raise Refusal("ptx-literal", "NaN/infinity are outside exact scalar semantics")
            rational = Fraction.from_float(value)
            return node("lit", rational.numerator, rational.denominator)
        _, slot, _ = self.value(text, "scalar")
        return node("reg", slot)

    def address(self):
        self.pop("[")
        name = self.register()
        _, slot, buffer = self.value(name, "pointer")
        self.pop("]")
        offset = node("ivar", slot)
        # A failed alignment check loops at this instruction. Any successful
        # Lean run therefore establishes alignment before dividing byte offsets.
        pc = len(self.code)
        aligned = node("eq", node("mod", offset, node("const", 4)), node("const", 0))
        self.code.append(node("branch", aligned, pc))
        return buffer, node("div", offset, node("const", 4))

    def predicate(self, op):
        dest = self.register()
        self.pop(",")
        a = self.integer()
        self.pop(",")
        b = self.integer()
        comparison = op.split(".")[1]
        if comparison in {"gt", "ge"}:
            a, b = b, a
            comparison = {"gt": "lt", "ge": "le"}[comparison]
        slot = self.assign(dest, "predicate", None)
        pc = len(self.code)
        self.code.extend(
            [
                node("branch", node(comparison, a, b), pc + 3),
                node("idx", slot, node("const", 1)),
                node("jump", pc + 4),
                node("idx", slot, node("const", 0)),
            ]
        )

    def instruction(self):
        if self.accept("@"):
            negate = self.accept("!")
            _, slot, _ = self.value(self.register(), "predicate")
            self.pop("bra")
            target = self.name()
            # Machine branch jumps on FALSE, PTX branches on its guard.
            predicate = node("ne" if negate else "eq", node("ivar", slot), node("const", 0))
            self.patches.append((len(self.code), target))
            self.code.append(node("branch", predicate, 0))
        else:
            op = self.pop()
            if op == "bra":
                self.patches.append((len(self.code), self.name()))
                self.code.append(node("jump", 0))
            elif op == "ld.param.u64":
                dest = self.register()
                self.pop(",")
                self.pop("[")
                param = self.name()
                self.pop("]")
                names = [b.name for b in self.task.buffers]
                if param not in names:
                    raise Refusal("ptx-signature", "unknown buffer parameter")
                self.assign(dest, "pointer", node("const", 0), names.index(param))
            elif op == "add.u64":
                dest = self.register()
                self.pop(",")
                _, slot, buffer = self.value(self.register(), "pointer")
                self.pop(",")
                offset = self.integer(64)
                self.assign(dest, "pointer", node("add", node("ivar", slot), offset), buffer)
            elif op in {"mov.u32", "mov.u64", "mul.wide.u32", "add.u32", "mul.lo.u32"}:
                dest = self.register()
                self.pop(",")
                expression = self.integer(64 if op == "mov.u64" else 32, special=op == "mov.u32")
                if not op.startswith("mov"):
                    self.pop(",")
                    expression = node(
                        "add" if op == "add.u32" else "mul", expression, self.integer()
                    )
                expected = (
                    {".b64", ".u64"} if op in {"mov.u64", "mul.wide.u32"} else {".b32", ".u32"}
                )
                if self.regs[dest] not in expected:
                    raise Refusal("ptx-type", "integer instruction destination width differs")
                self.assign(dest, "index", expression)
            elif re.fullmatch(r"setp\.(?:eq|ne|lt|le|gt|ge)\.u32", op):
                self.predicate(op)
            elif op == "ld.global.f32":
                dest = self.register()
                self.pop(",")
                buffer, index = self.address()
                self.assign(dest, "scalar", node("load", "global", buffer, index))
            elif op == "st.global.f32":
                buffer, index = self.address()
                self.pop(",")
                self.code.append(node("store", "global", buffer, index, self.scalar()))
            elif op in {"mov.f32", "add.rn.f32", "sub.rn.f32", "mul.rn.f32", "max.f32"}:
                dest = self.register()
                self.pop(",")
                expression = self.scalar()
                if op != "mov.f32":
                    self.pop(",")
                    expression = node("bin", op.split(".")[0], expression, self.scalar())
                self.assign(dest, "scalar", expression)
            elif op == "bar.sync":
                self.pop("0")
                self.code.append(node("barrier", "block"))
            elif op == "ret":
                self.code.append(node("halt"))
                self.pop(";")
                if self.peek() != "}":
                    raise Refusal("ptx-control", "one terminal ret is required")
                return
            else:
                raise Refusal("ptx-operation", "unsupported instruction " + op)
        self.pop(";")

    def read(self):
        if self.task.language != "ptx" or any(b.dtype != "float32" for b in self.task.buffers):
            raise Refusal("ptx-type", "this PTX subset requires float32 buffers")
        for expected in (".version", "8.0", ".target", "sm_80", ".address_size", "64"):
            self.pop(expected)
        self.accept(".visible")
        self.pop(".entry")
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("entry", "PTX entry differs from task")
        self.pop("(")
        for i, buffer in enumerate(self.task.buffers):
            if i:
                self.pop(",")
            self.pop(".param")
            self.pop(".u64")
            if self.name() != buffer.name:
                raise Refusal("ptx-signature", "parameter order/name differs from task")
        self.pop(")")
        self.pop("{")
        while self.peek() == ".reg":
            self.declare()
        while self.peek() != "}":
            if self.i + 1 < len(self.tokens) and self.tokens[self.i + 1].text == ":":
                name = self.name()
                self.pop(":")
                if name in self.labels:
                    raise Refusal("ptx-control", "duplicate label")
                self.labels[name] = len(self.code)
            else:
                self.instruction()
            if len(self.code) > 256:
                raise Refusal("ptx-capacity", "at most 256 lowered instructions accepted")
        self.pop("}")
        if self.peek() != "<eof>" or not self.code or self.code[-1].op != "halt":
            raise Refusal("ptx-syntax", "exactly one kernel with terminal ret required")
        for pc, label in self.patches:
            if label not in self.labels or self.labels[label] <= pc:
                raise Refusal("ptx-control", "only defined forward branch targets accepted")
            instr = self.code[pc]
            self.code[pc] = (
                node("jump", self.labels[label])
                if instr.op == "jump"
                else node("branch", instr.args[0], self.labels[label])
            )
        return Translation(entry, self.tokens, self.trailing, self.code, [])
