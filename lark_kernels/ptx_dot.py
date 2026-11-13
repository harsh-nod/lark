"""Lossless typed reader for the finite-execution PTX dot-product development model.

All labels and backward branches are retained and resolved to actual instruction
positions. Parsing is not a certificate; the source-bound loop/kernel proof is
a separate requirement. The legacy and published pointwise readers are unchanged.
"""

import ast
from dataclasses import dataclass
import json
import re

from . import gemv, ptx_pointwise
from .frontend import Token
from .ir import Refusal


TOKEN = re.compile(
    r"(?P<trivia>\s+|//[^\n]*(?:\n|$)|/\*[\s\S]*?\*/)"
    r"|(?P<token>0[fF][0-9a-fA-F]{8}|0[xX][0-9a-fA-F]+|\d+\.\d+|\d+"
    r"|%[A-Za-z_]\w*(?:\.[xyz])?|\$[A-Za-z_]\w*|\.?[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*"
    r"|[{}()[\];,:<>@!+\-])"
)
ARITIES = {"parameter": 2, "toGlobal": 2, "blockId": 1, "literal32": 2,
           "shiftLeft32": 3, "addSigned32": 3, "mulWideSigned32": 3, "addSigned64": 3,
           "loadHalf": 3, "fromHalf": 2, "literalFloat": 3, "binaryFloat": 4, "toHalf": 2,
           "storeHalf": 3, "compareNeSigned32": 3, "branch": 2, "ret": 0}


def tokenize(source):
    tokens, leading, position = [], "", 0
    while position < len(source):
        match = TOKEN.match(source, position)
        if not match:
            raise Refusal("ptx-dot-syntax", f"unsupported source at character {position}")
        if match.lastgroup == "trivia":
            leading += match.group()
        else:
            tokens.append(Token(leading, match.group()))
            leading = ""
        position = match.end()
    return tokens, leading


@dataclass
class Translation:
    entry: str
    tokens: list
    trailing: str
    parameters: list
    registers: dict
    labels: dict
    instructions: list

    def readback(self):
        return "".join(token.leading + token.text for token in self.tokens) + self.trailing

    def data(self):
        return {"entry": self.entry, "tokens": [[t.leading, t.text] for t in self.tokens],
                "trailing": self.trailing, "parameters": self.parameters, "registers": self.registers,
                "labels": self.labels, "instructions": self.instructions}

    def lean_program(self):
        return "[" + ", ".join(lean_instruction(ins) for ins in self.instructions) + "]"


def lean_instruction(instruction):
    if (not isinstance(instruction, (list, tuple)) or not instruction
            or type(instruction[0]) is not str or instruction[0] not in ARITIES):
        raise Refusal("ptx-dot-constructor", "unknown instruction constructor")
    tag, *args = instruction
    if len(args) != ARITIES[tag]:
        raise Refusal("ptx-dot-constructor", "instruction arity differs")
    pieces = []
    for i, value in enumerate(args):
        if tag in {"addSigned32", "addSigned64", "compareNeSigned32"} and i == 2:
            if (not isinstance(value, (list, tuple)) or len(value) != 2
                    or type(value[0]) is not str or value[0] not in {"reg", "imm"}
                    or type(value[1]) is not int):
                raise Refusal("ptx-dot-constructor", "typed integer operand required")
            kind, number = value
            width = 64 if tag == "addSigned64" else 32
            if not (0 <= number < 256 if kind == "reg" else -(2 ** (width - 1)) <= number < 2 ** (width - 1)):
                raise Refusal("ptx-dot-constructor", "integer operand out of range")
            pieces.append(f"(.{kind} ({number}))")
        elif tag == "binaryFloat" and i == 1:
            if type(value) is not str or value not in ptx_pointwise.BINARIES.values():
                raise Refusal("ptx-dot-constructor", "unknown scalar operator")
            pieces.append("." + value)
        else:
            signed = (tag == "mulWideSigned32" and i == 2 or tag == "loadHalf" and i == 2
                      or tag == "storeHalf" and i == 1 or tag == "literalFloat" and i == 1)
            if type(value) is not int or (not signed and value < 0):
                raise Refusal("ptx-dot-constructor", "integer instruction operand required")
            if tag == "literalFloat" and i == 2 and value == 0:
                raise Refusal("ptx-dot-constructor", "nonzero literal denominator required")
            pieces.append(f"({value})")
    return "(." + tag + (" " + " ".join(pieces) if pieces else "") + ")"


class Reader(ptx_pointwise.Reader):
    def __init__(self, source, task):
        self.tokens, self.trailing = tokenize(source)
        self.i, self.task = 0, task
        self.code, self.regs, self.labels, self.patches = [], {}, {}, []

    def declare(self):
        if self.i + 1 >= len(self.tokens) or self.tokens[self.i + 1].text != ".pred":
            return super().declare()
        self.pop(".reg")
        self.pop(".pred")
        name = self.pop()
        names = [name]
        if self.accept("<"):
            if name != "%p":
                raise Refusal("ptx-dot-register", "predicate declaration prefix differs")
            count = self.pop()
            if not re.fullmatch(r"[1-9][0-9]*", count) or not 1 <= int(count) <= 128:
                raise Refusal("ptx-dot-capacity", "predicate arrays require 1..128 entries")
            self.pop(">")
            names = [name + str(i) for i in range(int(count))]
        self.pop(";")
        for name in names:
            match = re.fullmatch(r"%p(0|[1-9][0-9]*)", name)
            if not match or int(match[1]) >= 256 or name in self.regs or len(self.regs) >= 256:
                raise Refusal("ptx-dot-register", "duplicate, aliased or unsupported predicate")
            self.regs[name] = ["predicate", int(match[1])]

    def integer(self, width=32, signed=True):
        negative = self.accept("-")
        text = self.pop()
        if not re.fullmatch(r"0|[1-9][0-9]*|0[xX][0-9a-fA-F]+", text):
            raise Refusal("ptx-dot-literal", "canonical integer literal required")
        value = int(text, 16 if text.lower().startswith("0x") else 10)
        value = -value if negative else value
        lower, upper = (-(2 ** (width - 1)), 2 ** (width - 1)) if signed else (0, 2 ** width)
        if not lower <= value < upper:
            raise Refusal("ptx-dot-literal", "integer immediate exceeds its instruction width")
        return value

    def operand(self, bank):
        if self.peek().startswith("%"):
            return ["reg", self.reg(bank)]
        return ["imm", self.integer(32 if bank == "i32" else 64)]

    def address(self):
        self.pop("[")
        register = self.reg("i64")
        offset = self.integer(64) if self.accept("+") else 0
        self.pop("]")
        return register, offset

    def instruction(self):
        op = self.peek()
        if op not in {"mov.u32", "shl.b32", "add.s32", "add.s64", "ld.global.u16",
                      "st.global.u16", "setp.ne.s32", "@"}:
            super().instruction()
            rename = {"mulWideS32": "mulWideSigned32", "literal": "literalFloat", "binary": "binaryFloat"}
            self.code[-1][0] = rename.get(self.code[-1][0], self.code[-1][0])
            return
        self.pop()
        if op == "mov.u32":
            dest = self.reg("i32")
            self.comma()
            ins = (["blockId", dest] if self.accept("%ctaid.x")
                   else ["literal32", dest, self.integer(signed=False)])
        elif op == "shl.b32":
            dest = self.reg("i32")
            self.comma()
            left = self.reg("i32")
            self.comma()
            ins = ["shiftLeft32", dest, left, self.integer(signed=False)]
        elif op in {"add.s32", "add.s64", "setp.ne.s32"}:
            bank = "i64" if op == "add.s64" else "i32"
            dest = self.reg("predicate" if op == "setp.ne.s32" else bank)
            self.comma()
            left = self.reg(bank)
            self.comma()
            tag = {"add.s32": "addSigned32", "add.s64": "addSigned64", "setp.ne.s32": "compareNeSigned32"}[op]
            ins = [tag, dest, left, self.operand(bank)]
        elif op == "ld.global.u16":
            dest = self.reg("half")
            self.comma()
            ins = ["loadHalf", dest, *self.address()]
        elif op == "st.global.u16":
            address = self.address()
            self.comma()
            ins = ["storeHalf", *address, self.reg("half")]
        else:
            predicate = self.reg("predicate")
            self.pop("bra")
            label = self.pop()
            if not re.fullmatch(r"\$[A-Za-z_]\w*", label):
                raise Refusal("ptx-dot-label", "closed local branch label required")
            self.patches.append((len(self.code), label))
            ins = ["branch", predicate, None]
        self.pop(";")
        self.code.append(ins)
        if len(self.code) > 256:
            raise Refusal("ptx-dot-capacity", "at most 256 source instructions")

    def group(self, depth=0):
        if depth > 8:
            raise Refusal("ptx-dot-capacity", "inline grouping is too deep")
        while self.peek() != "}":
            if self.accept("{"):
                self.group(depth + 1)
                self.pop("}")
            elif self.peek().startswith("$"):
                label = self.pop()
                self.pop(":")
                if label in self.labels:
                    raise Refusal("ptx-dot-label", "duplicate local label")
                self.labels[label] = len(self.code)
            else:
                self.instruction()

    def read(self):
        for expected in (".version", "8.8", ".target", "sm_80", ".address_size", "64", ".visible", ".entry"):
            self.pop(expected)
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("ptx-dot-entry", "entry differs from unchanged CUDA contract")
        self.parameters = []
        self.pop("(")
        for i in range(len(self.task.buffers)):
            if i:
                self.comma()
            self.pop(".param")
            self.pop(".u64")
            self.parameters.append(self.name())
        if len(set(self.parameters)) != len(self.task.buffers):
            raise Refusal("ptx-dot-parameter", "distinct positional buffer parameters required")
        self.pop(")")
        self.pop("{")
        while self.peek() == ".reg":
            self.declare()
        self.group()
        self.pop("}")
        if self.peek() != "<eof>":
            raise Refusal("ptx-dot-eof", "trailing declarations or tokens")
        if not self.code or self.code[-1] != ["ret"] or self.code.count(["ret"]) != 1:
            raise Refusal("ptx-dot-control", "exactly one final ret required")
        for index, label in self.patches:
            if label not in self.labels or self.labels[label] >= len(self.code):
                raise Refusal("ptx-dot-label", "undefined or out-of-range branch label")
            self.code[index][2] = self.labels[label]
        return Translation(entry, self.tokens, self.trailing, self.parameters,
                           dict(sorted(self.regs.items())), self.labels, self.code)


def translate(source, cuda_task_source):
    task = gemv.parse_task(cuda_task_source)
    if task.language != "cuda" or task.warp != 32 or task.block != 1:
        raise Refusal("ptx-dot-contract", "unchanged scalar CUDA warp32 GEMV contract required")
    result = Reader(source, task).read()
    if result.readback().encode() != source.encode():
        raise Refusal("ptx-dot-readback", "lossless source readback differs")
    return task, result


PROFILE = "source-bound-compiled-gemv-fp16-v1"
TAGS = ("source_program", "reference_body", "launch", "race_free",
        "segment_equivalence", "kernel_eq_spec")
REFERENCE = ("toHalf", ("matmul", ("fromHalf", ("input", 0)), ("fromHalf", ("input", 1))))


def prepare(source, reference, cuda_task_source):
    task, translation = translate(source, cuda_task_source)
    if ([buffer.shape for buffer in task.buffers] != [(512, 1024), (1024, 1), (512, 1)]
            or [buffer.name for buffer in task.buffers] != ["a", "b", "out"]):
        raise Refusal("ptx-dot-contract", "the unchanged 512x1024 FP16 GEMV contract is required")
    canonical = ast.parse("import torch\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-dot-reference", "invalid Python reference syntax") from error
    if ast.dump(actual) != ast.dump(canonical):
        raise Refusal("ptx-dot-reference", "the complete closed FP16 matrix-vector reference AST is required")
    return task, translation, json.loads(json.dumps(REFERENCE))


def lean_reference(body):
    try:
        encoded = json.dumps(body, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise Refusal("ptx-dot-reference", "a closed JSON tensor reference AST is required") from error
    if encoded != json.dumps(REFERENCE, separators=(",", ":")):
        raise Refusal("ptx-dot-reference", "unsupported closed tensor reference AST")
    return "(.toHalf (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))))"


def render(task, translation, reference_body):
    if ([buffer.shape for buffer in task.buffers] != [(512, 1024), (1024, 1), (512, 1)]
            or (task.grid, task.block, task.warp) != (512, 1, 32)
            or tuple(task.fuel) != (4102, 1, 1, 1)):
        raise Refusal("ptx-dot-contract", "fixed source proof dimensions, geometry or CUDA fuel differ")
    return f"""import Lark.PtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxDotCertificate
open LarkNonlinear
def program : List LarkPtxDot.Instruction := {translation.lean_program()}
def referenceBody : LarkPtxDot.Gemv.TensorReference := {lean_reference(reference_body)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (LarkPtxDot.Gemv.evaluateReference ops input referenceBody).getD []
theorem source_program : program = LarkPtxDot.Gemv.program := by rfl
theorem reference_body : referenceBody = LarkPtxDot.Gemv.referenceBody := by rfl
theorem launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPtxDot.Gemv.LaneSequence ops program 0 512
      (initial (LarkPtxDot.Gemv.layout 512) input outside)
      (LarkPtxDot.Gemv.finalState ops input outside) := by
  rw [source_program]
  exact LarkPtxDot.Gemv.launch_execution ops input outside
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (LarkPtxDot.Gemv.geometry 512)
      (LarkPtxDot.Gemv.finalState ops input outside).trace = true :=
  LarkPtxDot.Gemv.launch_raceFree ops input outside
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (LarkPtxDot.Gemv.layout 512) (LarkPtxDot.Gemv.finalState ops input outside) =
      some (spec ops input) := by
  unfold spec
  rw [reference_body, LarkPtxDot.Gemv.evaluate_reference_body]
  exact LarkPtxDot.Gemv.final_extract ops input outside
theorem kernel_eq_spec (ops : Ops α) : LarkPtxDot.Gemv.Correct ops program (spec ops) := by
  intro input outside
  exact ⟨LarkPtxDot.Gemv.finalState ops input outside, launch ops input outside,
    race_free ops input outside, segment_equivalence ops input outside⟩
""" + "".join("#print axioms LarkPtxDotCertificate." + tag + "\n" for tag in TAGS) + (
        "end LarkPtxDotCertificate\n")
