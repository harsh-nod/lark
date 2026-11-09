"""Strict CUDA/HIP reader, lossless token data, and fixed lowering to flat instructions."""

from __future__ import annotations

from dataclasses import dataclass
import re

from .ir import Node, Refusal, Task, literal, node


TOKEN = re.compile(
    r"(?P<trivia>\s+|//[^\n]*(?:\n|$)|/\*[\s\S]*?\*/)"
    r'|(?P<token>"C"|(?:\d+\.\d*|\.\d+|\d+)(?:[eE][+-]?\d+)?[fF]?'
    r"|[A-Za-z_]\w*|::|<=|>=|==|!=|\+\+|--|\+=|-=|\*=|[{}()[\];,*+/%<>=.\-])"
)


@dataclass(frozen=True)
class Token:
    leading: str
    text: str


@dataclass
class Translation:
    entry: str
    tokens: list[Token]
    trailing: str
    program: list[Node]
    shared: list[tuple[str, int]]

    def readback(self):
        return "".join(t.leading + t.text for t in self.tokens) + self.trailing

    def data(self):
        return {
            "entry": self.entry,
            "tokens": [[t.leading, t.text] for t in self.tokens],
            "trailing": self.trailing,
            "program": [n.data() for n in self.program],
            "shared": self.shared,
        }


def tokenize(source: str):
    tokens, leading, pos = [], "", 0
    while pos < len(source):
        m = TOKEN.match(source, pos)
        if not m:
            raise Refusal(
                "syntax", f"unrecognized source at byte {pos}: {source[pos : pos + 30]!r}"
            )
        if m.lastgroup == "trivia":
            leading += m.group()
        else:
            tokens.append(Token(leading, m.group()))
            leading = ""
        pos = m.end()
    return tokens, leading


class Reader:
    def __init__(self, source: str, task: Task):
        self.tokens, self.trailing = tokenize(source)
        self.i, self.task = 0, task
        self.symbols: dict[str, tuple[str, int, bool]] = {}
        self.code: list[Node] = []
        self.shared: list[tuple[str, int]] = []
        self.nindex = self.nreg = 0

    def peek(self):
        return self.tokens[self.i].text if self.i < len(self.tokens) else "<eof>"

    def pop(self, expected=None):
        s = self.peek()
        if s == "<eof>" or (expected is not None and s != expected):
            raise Refusal("syntax", f"token {self.i}: expected {expected!r}, got {s!r}")
        self.i += 1
        return s

    def accept(self, s):
        if self.peek() == s:
            self.pop()
            return True
        return False

    def name(self):
        s = self.pop()
        reserved = {
            "if",
            "else",
            "while",
            "for",
            "do",
            "return",
            "break",
            "continue",
            "float",
            "int",
            "const",
            "void",
            "extern",
            "unsigned",
            "signed",
            "struct",
            "class",
            "auto",
            "threadIdx",
            "blockIdx",
            "blockDim",
            "fmaxf",
            "__syncthreads",
            "__syncwarp",
            "grid_sync",
        }
        if not re.fullmatch(r"[A-Za-z_]\w*", s) or s in reserved:
            raise Refusal("syntax", f"expected identifier, got {s}")
        return s

    def declare(self, name, kind, id, constant=False):
        if name in self.symbols:
            raise Refusal("shadowing", f"duplicate or shadowed name {name}")
        self.symbols[name] = (kind, id, constant)

    def expr(self, mode, precedence=0):
        s = self.pop()
        if s == "(":
            lhs = self.expr(mode)
            self.pop(")")
        elif s == "-":
            rhs = self.expr(mode, 30)
            lhs = (
                node("sub", node("const", 0), rhs)
                if mode == "index"
                else node("bin", "sub", literal(0), rhs)
            )
        elif re.fullmatch(r"(?:\d+\.\d*|\.\d+|\d+)(?:[eE][+-]?\d+)?[fF]?", s):
            if mode == "index":
                if not s.isdecimal() or int(s) > 2**31 - 1:
                    raise Refusal("integer", "indices require signed 32-bit integer literals")
                lhs = node("const", int(s))
            else:
                lhs = literal(s.rstrip("fF"))
        elif s in {"threadIdx", "blockIdx", "blockDim"}:
            if mode != "index":
                raise Refusal("conversion", "integer-to-float casts are not implemented")
            self.pop(".")
            self.pop("x")
            lhs = node({"threadIdx": "tid", "blockIdx": "bid", "blockDim": "bdim"}[s])
        elif s == "fmaxf" and mode == "scalar":
            self.pop("(")
            a = self.expr(mode)
            self.pop(",")
            b = self.expr(mode)
            self.pop(")")
            lhs = node("bin", "max", a, b)
        elif s in self.symbols:
            kind, id, _ = self.symbols[s]
            if kind in {"global", "shared"} and mode == "scalar":
                self.pop("[")
                ix = self.expr("index")
                self.pop("]")
                lhs = node("load", kind, id, ix)
            elif kind == mode:
                lhs = node("ivar" if kind == "index" else "reg", id)
            else:
                raise Refusal("type", f"{s} is {kind}, used as {mode}")
        else:
            raise Refusal("operation", f"unsupported expression {s!r}")
        levels = {"+": 10, "-": 10, "*": 20, "/": 20, "%": 20}
        while self.peek() in levels and levels[self.peek()] > precedence:
            op = self.pop()
            rhs = self.expr(mode, levels[op])
            name = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod"}[op]
            if mode == "scalar":
                if name in {"div", "mod"}:
                    raise Refusal("operation", "scalar division/remainder is not implemented")
                lhs = node("bin", name, lhs, rhs)
            else:
                lhs = node(name, lhs, rhs)
        return lhs

    def predicate(self):
        self.pop("(")
        a = self.expr("index")
        op = self.pop()
        if op not in {"<", "<=", ">", ">=", "==", "!="}:
            raise Refusal("control", "only comparisons of integer expressions are supported")
        b = self.expr("index")
        self.pop(")")
        if op in {">", ">="}:
            a, b = b, a
            op = "<" if op == ">" else "<="
        return node({"<": "lt", "<=": "le", "==": "eq", "!=": "ne"}[op], a, b)

    def body(self):
        self.pop("{")
        while self.peek() != "}":
            self.statement()
        self.pop("}")

    def statement(self):
        s = self.peek()
        if s == "{":
            self.body()
        elif s in {"if", "while"}:
            self.pop()
            start = len(self.code)
            p = self.predicate()
            self.code.append(node("branch", p, 0))
            self.body()
            if s == "while":
                self.code.append(node("jump", start))
            if s == "if" and self.accept("else"):
                jump = len(self.code)
                self.code.append(node("jump", 0))
                self.code[start] = node("branch", p, len(self.code))
                self.body()
                self.code[jump] = node("jump", len(self.code))
            else:
                self.code[start] = node("branch", p, len(self.code))
        elif s == "__shared__":
            self.pop()
            self.pop("float")
            name = self.name()
            self.pop("[")
            size = self.pop()
            if not size.isdecimal() or not 0 < int(size) <= 4096:
                raise Refusal("shape", "shared buffers require a literal size in 1..4096")
            self.pop("]")
            self.pop(";")
            self.declare(name, "shared", len(self.shared))
            self.shared.append((name, int(size)))
        elif s in {"const", "int", "float"}:
            constant = self.accept("const")
            ty = self.pop()
            if ty not in {"int", "float"}:
                raise Refusal("type", f"unsupported local type {ty}")
            name = self.name()
            mode = "index" if ty == "int" else "scalar"
            id = self.nindex if ty == "int" else self.nreg
            self.declare(name, mode, id, constant)
            if mode == "index":
                self.nindex += 1
            else:
                self.nreg += 1
            if self.accept("="):
                self.code.append(node("idx" if ty == "int" else "set", id, self.expr(mode)))
            elif constant:
                raise Refusal("syntax", "const variables require an initializer")
            self.pop(";")
        elif s in {"__syncthreads", "__syncwarp", "grid_sync"}:
            self.pop()
            self.pop("(")
            self.pop(")")
            self.pop(";")
            if s == "grid_sync":
                raise Refusal("grid-barrier", "no hardware-calibrated cooperative barrier template")
            if s == "__syncwarp" and (self.task.language != "cuda" or self.task.block % 32):
                raise Refusal(
                    "warp-mask", "__syncwarp requires CUDA blocks with complete 32-lane warps"
                )
            self.code.append(node("barrier", "block" if s == "__syncthreads" else "warp"))
        elif s == "return":
            self.pop()
            self.pop(";")
            self.code.append(node("halt"))
        elif s in self.symbols:
            name = self.pop()
            kind, id, constant = self.symbols[name]
            if kind in {"global", "shared"}:
                if constant:
                    raise Refusal("type", f"write through const pointer {name}")
                self.pop("[")
                ix = self.expr("index")
                self.pop("]")
                self.pop("=")
                self.code.append(node("store", kind, id, ix, self.expr("scalar")))
            else:
                if constant:
                    raise Refusal("type", f"assignment to const {name}")
                op = self.pop()
                if op == "=":
                    value = self.expr(kind)
                elif op in {"++", "--", "+=", "-=", "*="}:
                    old = node("ivar" if kind == "index" else "reg", id)
                    rhs = (
                        (node("const", 1) if kind == "index" else literal(1))
                        if op in {"++", "--"}
                        else self.expr(kind)
                    )
                    binary = "add" if op in {"++", "+="} else "sub" if op in {"--", "-="} else "mul"
                    value = (
                        node(binary, old, rhs) if kind == "index" else node("bin", binary, old, rhs)
                    )
                else:
                    raise Refusal("operation", f"unsupported assignment {op}")
                self.code.append(node("idx" if kind == "index" else "set", id, value))
            self.pop(";")
        else:
            raise Refusal("operation", f"unsupported statement starting with {s!r}")

    def read(self):
        if self.accept("extern"):
            self.pop('"C"')
        self.pop("__global__")
        self.pop("void")
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("entry", f"expected {self.task.entry}, got {entry}")
        self.pop("(")
        for id, b in enumerate(self.task.buffers):
            if id:
                self.pop(",")
            constant = self.accept("const")
            self.pop("float")
            self.pop("*")
            name = self.name()
            if name != b.name:
                raise Refusal("signature", f"argument {id}: expected {b.name}, got {name}")
            self.declare(name, "global", id, constant)
        self.pop(")")
        self.body()
        if self.peek() != "<eof>":
            raise Refusal("syntax", "expected exactly one kernel and no trailing declarations")
        self.code.append(node("halt"))
        result = Translation(entry, self.tokens, self.trailing, self.code, self.shared)
        return result


def translate(source: str, task: Task) -> Translation:
    result = Reader(source, task).read()
    if result.readback().encode("utf-8") != source.encode("utf-8"):
        raise Refusal("readback", "token data does not reconstruct the original source bytes")
    return result
