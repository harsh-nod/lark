"""Source reader and immutable theorem for the finite FP16 PTX pointwise profile.

This separate profile consumes PTX 8.8/sm_80 and an unchanged CUDA reference
contract from the compiler study. It does not change the older PTX reader or
its certificates. The finite model executes every parsed instruction; the
contract's existing CUDA fuel is retained as data for the separate CUDA model.
"""

from dataclasses import dataclass
from fractions import Fraction
import math
import re
import struct

from . import pointwise, ptx
from .ir import Refusal


PROFILE = "ptx-fp16-pointwise-finite-v1"
TARGET = "Lark.PtxPointwise"
TAGS = ("source_program", "reference_body", "launch", "race_free",
        "segment_equivalence", "kernel_eq_spec")
BANKS = {".b16": ("rs", "half"), ".b32": ("r", "i32"),
         ".b64": ("rd", "i64"), ".f32": ("f", "scalar")}
BINARIES = {"max.f32": "max", "add.rn.f32": "add",
            "sub.rn.f32": "sub", "mul.rn.f32": "mul"}
ARITIES = {"parameter": 2, "toGlobal": 2, "blockId": 1, "mulWideS32": 3,
           "addPointerS64": 3, "loadHalf": 2, "fromHalf": 2, "literal": 3,
           "binary": 4, "toHalf": 2, "storeHalf": 2, "ret": 0}


@dataclass
class Translation:
    entry: str
    tokens: list
    trailing: str
    parameters: list
    registers: dict
    instructions: list

    def readback(self):
        return "".join(token.leading + token.text for token in self.tokens) + self.trailing

    def data(self):
        return {"entry": self.entry, "tokens": [[t.leading, t.text] for t in self.tokens],
                "trailing": self.trailing, "parameters": self.parameters,
                "registers": self.registers, "instructions": self.instructions}

    def lean_program(self):
        return "[" + ", ".join(lean_instruction(ins) for ins in self.instructions) + "]"


class Reader(ptx.Reader):
    """Closed instruction grammar; captured source is never executed."""

    def declare(self):
        self.pop(".reg")
        ty = self.pop()
        if ty not in BANKS:
            raise Refusal("ptx-pointwise-type", "unsupported declaration " + ty)
        prefix, bank = BANKS[ty]
        name = self.pop()
        names = [name]
        if self.accept("<"):
            if name != "%" + prefix:
                raise Refusal("ptx-pointwise-register", "declaration prefix/type differs")
            count = self.pop()
            if not count.isdecimal() or not 1 <= int(count) <= 128:
                raise Refusal("ptx-pointwise-capacity", "register arrays require 1..128 entries")
            self.pop(">")
            names = [name + str(i) for i in range(int(count))]
        self.pop(";")
        for name in names:
            match = re.fullmatch("%" + prefix + r"(0|[1-9][0-9]*)", name)
            if not match or int(match[1]) >= 256 or name in self.regs or len(self.regs) >= 256:
                raise Refusal("ptx-pointwise-register", "duplicate, aliased or unsupported register")
            self.regs[name] = [bank, int(match[1])]

    def reg(self, bank):
        name = self.register()
        actual, index = self.regs[name]
        if actual != bank:
            raise Refusal("ptx-pointwise-type", name + ": expected " + bank)
        return index

    def comma(self):
        self.pop(",")

    def address(self):
        self.pop("[")
        index = self.reg("i64")
        self.pop("]")
        return index

    def immediate(self):
        text = self.pop()
        if not re.fullmatch(r"[0-9]+|0[xX][0-9a-fA-F]+", text):
            raise Refusal("ptx-pointwise-literal", "nonnegative integer immediate required")
        value = int(text, 16 if text.lower().startswith("0x") else 10)
        if not 0 <= value < 2147483648:
            raise Refusal("ptx-pointwise-literal", "immediate is outside the signed32 subset")
        return value

    def literal(self):
        text = self.pop()
        if not re.fullmatch(r"0[fF][0-9a-fA-F]{8}", text):
            raise Refusal("ptx-pointwise-literal", "finite hexadecimal float32 literal required")
        value = struct.unpack(">f", bytes.fromhex(text[2:]))[0]
        if not math.isfinite(value):
            raise Refusal("ptx-pointwise-literal", "non-finite scalar literal")
        rational = Fraction.from_float(value)
        return rational.numerator, rational.denominator

    def instruction(self):
        op = self.pop()
        if op == "ld.param.u64":
            dest = self.reg("i64")
            self.comma()
            self.pop("[")
            parameter = self.name()
            self.pop("]")
            if parameter not in self.parameters:
                raise Refusal("ptx-pointwise-parameter", "unknown parameter")
            ins = ["parameter", dest, self.parameters.index(parameter)]
        elif op == "cvta.to.global.u64":
            dest = self.reg("i64")
            self.comma()
            ins = ["toGlobal", dest, self.reg("i64")]
        elif op == "mov.u32":
            dest = self.reg("i32")
            self.comma()
            self.pop("%ctaid.x")
            ins = ["blockId", dest]
        elif op == "mul.wide.s32":
            dest = self.reg("i64")
            self.comma()
            source = self.reg("i32")
            self.comma()
            ins = ["mulWideS32", dest, source, self.immediate()]
        elif op == "add.s64":
            dest = self.reg("i64")
            self.comma()
            left = self.reg("i64")
            self.comma()
            ins = ["addPointerS64", dest, left, self.reg("i64")]
        elif op == "ld.global.u16":
            dest = self.reg("half")
            self.comma()
            ins = ["loadHalf", dest, self.address()]
        elif op == "cvt.f32.f16":
            dest = self.reg("scalar")
            self.comma()
            ins = ["fromHalf", dest, self.reg("half")]
        elif op == "mov.f32":
            dest = self.reg("scalar")
            self.comma()
            ins = ["literal", dest, *self.literal()]
        elif op in BINARIES:
            dest = self.reg("scalar")
            self.comma()
            left = self.reg("scalar")
            self.comma()
            ins = ["binary", dest, BINARIES[op], left, self.reg("scalar")]
        elif op == "cvt.rn.f16.f32":
            dest = self.reg("half")
            self.comma()
            ins = ["toHalf", dest, self.reg("scalar")]
        elif op == "st.global.u16":
            dest = self.address()
            self.comma()
            ins = ["storeHalf", dest, self.reg("half")]
        elif op == "ret":
            ins = ["ret"]
        else:
            raise Refusal("ptx-pointwise-operation", "unsupported instruction " + op)
        self.pop(";")
        self.code.append(ins)
        if len(self.code) > 256:
            raise Refusal("ptx-pointwise-capacity", "at most 256 instructions")

    def group(self, depth=0):
        if depth > 8:
            raise Refusal("ptx-pointwise-capacity", "inline grouping is too deep")
        while self.peek() != "}":
            if self.accept("{"):
                self.group(depth + 1)
                self.pop("}")
            else:
                self.instruction()

    def read(self):
        for expected in (".version", "8.8", ".target", "sm_80", ".address_size", "64",
                         ".visible", ".entry"):
            self.pop(expected)
        entry = self.name()
        if entry != self.task.entry:
            raise Refusal("ptx-pointwise-entry", "entry differs from the unchanged contract")
        self.parameters = []
        self.pop("(")
        for i in range(2):
            if i:
                self.comma()
            self.pop(".param")
            self.pop(".u64")
            self.parameters.append(self.name())
        if len(set(self.parameters)) != 2:
            raise Refusal("ptx-pointwise-parameter", "distinct positional buffer parameters required")
        self.pop(")")
        self.pop("{")
        while self.peek() == ".reg":
            self.declare()
        self.group()
        self.pop("}")
        if self.peek() != "<eof>":
            raise Refusal("ptx-pointwise-eof", "trailing declarations or tokens")
        if not self.code or self.code[-1] != ["ret"] or self.code.count(["ret"]) != 1:
            raise Refusal("ptx-pointwise-control", "exactly one final ret is required")
        result = Translation(entry, self.tokens, self.trailing, self.parameters,
                             dict(sorted(self.regs.items())), self.code)
        return result


def lean_instruction(ins):
    if (not isinstance(ins, (list, tuple)) or not ins or type(ins[0]) is not str
            or ins[0] not in ARITIES):
        raise Refusal("ptx-pointwise-constructor", "unknown instruction constructor")
    op, *args = ins
    if len(args) != ARITIES[op]:
        raise Refusal("ptx-pointwise-constructor", "instruction arity differs")
    integers = args
    if op == "binary":
        if args[1] not in BINARIES.values():
            raise Refusal("ptx-pointwise-constructor", "unsupported scalar operation")
        integers = [args[0], *args[2:]]
    if any(type(value) is not int for value in integers):
        raise Refusal("ptx-pointwise-constructor", "instruction operands must be integers")
    if op == "literal":
        if args[0] < 0 or args[2] <= 0:
            raise Refusal("ptx-pointwise-constructor", "invalid register/literal denominator")
    elif any(value < 0 for value in integers):
        raise Refusal("ptx-pointwise-constructor", "nonnegative instruction operand required")
    if op == "literal":
        d, n, q = args
        return f"(.literal {d} ({n}) {q})"
    if op == "binary":
        d, binary, a, b = args
        return f"(.binary {d} .{binary} {a} {b})"
    # All remaining fields were parsed from declared, nonnegative register IDs,
    # positional parameters or the bounded signed32 immediate.
    return "." + op + (" " + " ".join(map(str, args)) if args else "")


def prepare(source, reference, cuda_task_source):
    task = pointwise.parse_task(cuda_task_source)
    if task.language != "cuda" or task.warp != 32 or task.block != 1:
        raise Refusal("ptx-pointwise-contract", "unchanged scalar CUDA/warp32 reference contract required")
    result = Reader(source, task).read()
    if result.readback().encode() != source.encode():
        raise Refusal("ptx-pointwise-readback", "source token reconstruction differs")
    reference_body = pointwise.reference_body(reference, task)
    pointwise.scalar(reference_body)
    return task, result, reference_body


def render(task, translation, reference_body):
    n = task.buffers[0].size
    return f"""import {TARGET}
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxCertificate
open LarkNonlinear
def elements : Nat := {n}
def program : List LarkPtxPointwise.Instruction := {translation.lean_program()}
def referenceBody : LarkPointwise.Scalar := {pointwise.scalar(reference_body)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkPointwise.spec ops referenceBody elements input
theorem source_program : program = LarkPtxPointwise.program := by rfl
theorem reference_body : referenceBody = LarkPtxPointwise.body := by rfl
theorem launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPtxPointwise.launch ops elements program input outside =
      some (LarkPtxPointwise.partialState ops elements input outside elements) := by
  rw [source_program]
  exact LarkPtxPointwise.launch_eq ops elements input outside (by dsimp [elements]; omega)
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (LarkPointwise.geometry elements 32)
      (LarkPtxPointwise.partialState ops elements input outside elements).trace = true := by
  exact LarkPtxPointwise.race_free ops elements input outside
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (LarkPointwise.layout elements)
      (LarkPtxPointwise.partialState ops elements input outside elements) = some (spec ops input) := by
  unfold spec
  rw [reference_body]
  exact LarkPtxPointwise.final_extract ops elements input outside
theorem kernel_eq_spec (ops : Ops α) :
    LarkPtxPointwise.Correct ops elements program (spec ops) := by
  intro input outside
  exact ⟨LarkPtxPointwise.partialState ops elements input outside elements,
    launch ops input outside, race_free ops input outside, segment_equivalence ops input outside⟩
""" + "".join("#print axioms LarkPtxCertificate." + name + "\n" for name in TAGS) + (
        "end LarkPtxCertificate\n")
