"""Lossless full-size compiled RoPE input for a separate development proof.

This reader preserves both branches and all predicate operations. Parsing alone
does not establish execution, a certificate, IEEE behavior or a model outcome.
"""

import ast
from dataclasses import dataclass
import re

from . import ptx_matrix, rotary
from .ir import Refusal


OPERATIONS = {
    "setp.eq.b32": "compareEqBits32", "mov.pred": "predicateLiteral",
    "xor.pred": "predicateXor", "not.pred": "predicateNot", "bra.uni": "branchAlways",
}


def lean_instruction(instruction):
    if not isinstance(instruction, (list, tuple)) or not instruction or type(instruction[0]) is not str:
        raise Refusal("ptx-rotary-constructor", "typed instruction data required")
    tag, *args = instruction
    if tag not in OPERATIONS.values():
        return "(.base " + ptx_matrix.lean_instruction(instruction) + ")"
    arity = {"compareEqBits32": 3, "predicateLiteral": 2, "predicateXor": 3,
             "predicateNot": 2, "branchAlways": 1}[tag]
    if len(args) != arity:
        raise Refusal("ptx-rotary-constructor", "instruction arity differs")
    registers = args[:2] if tag == "compareEqBits32" else args[:1] if tag == "predicateLiteral" else args
    if any(type(value) is not int or not 0 <= value < 256 for value in registers):
        raise Refusal("ptx-rotary-constructor", "register or instruction index is outside 0..255")
    if tag == "compareEqBits32":
        operand = args[2]
        if (not isinstance(operand, (list, tuple)) or len(operand) != 2
                or type(operand[0]) is not str or operand[0] not in {"reg", "imm"}
                or type(operand[1]) is not int
                or not (0 <= operand[1] < 256 if operand[0] == "reg" else -(2**31) <= operand[1] < 2**31)):
            raise Refusal("ptx-rotary-constructor", "typed 32-bit operand required")
        return f"(.compareEqBits32 {args[0]} {args[1]} (.{operand[0]} ({operand[1]})))"
    if tag == "predicateLiteral":
        if type(args[1]) is not bool:
            raise Refusal("ptx-rotary-constructor", "a typed predicate literal is required")
        return f"(.predicateLiteral {args[0]} {'true' if args[1] else 'false'})"
    return "(." + tag + " " + " ".join(str(value) for value in args) + ")"


@dataclass
class Translation(ptx_matrix.Translation):
    def lean_program(self):
        return "[" + ", ".join(lean_instruction(ins) for ins in self.instructions) + "]"


class Reader(ptx_matrix.Reader):
    def __init__(self, source, task):
        super().__init__(source, task)
        self.unconditional_patches = []

    def instruction(self):
        op = self.peek()
        if op not in OPERATIONS:
            return super().instruction()
        self.pop()
        if op == "bra.uni":
            label = self.pop()
            if not re.fullmatch(r"\$[A-Za-z_]\w*", label):
                raise Refusal("ptx-rotary-label", "closed local branch label required")
            self.unconditional_patches.append((len(self.code), label))
            instruction = ["branchAlways", None]
        else:
            destination = self.reg("predicate")
            self.comma()
            if op == "setp.eq.b32":
                left = self.reg("i32")
                self.comma()
                instruction = ["compareEqBits32", destination, left, self.operand("i32")]
            elif op == "mov.pred":
                value = self.integer(signed=False)
                if value not in (0, 1):
                    raise Refusal("ptx-rotary-predicate", "predicate literal must be zero or one")
                instruction = ["predicateLiteral", destination, bool(value)]
            elif op == "not.pred":
                instruction = ["predicateNot", destination, self.reg("predicate")]
            else:
                left = self.reg("predicate")
                self.comma()
                instruction = ["predicateXor", destination, left, self.reg("predicate")]
        self.pop(";")
        self.code.append(instruction)
        if len(self.code) > 256:
            raise Refusal("ptx-rotary-capacity", "at most 256 source instructions")

    def read(self):
        parsed = super().read()
        for index, label in self.unconditional_patches:
            if label not in self.labels or self.labels[label] >= len(self.code):
                raise Refusal("ptx-rotary-label", "undefined or out-of-range branch label")
            self.code[index][1] = self.labels[label]
        return Translation(**vars(parsed))


def fixed_task(task):
    if (task.language != "cuda"
            or [b.name for b in task.buffers] != ["x", "cosine", "sine", "out"]
            or [b.shape for b in task.buffers] != [(256, 128), (256, 64), (256, 64), (256, 128)]
            or [b.dtype for b in task.buffers] != ["float16"] * 4
            or (task.grid, task.block, task.warp) != (32768, 1, 32)
            or tuple(task.fuel) != (8, 1, 1, 1)
            or any(type(value) is not int for value in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-rotary-contract", "unchanged full-size interleaved RoPE CUDA contract required")


def prepare(source, reference, contract):
    task = rotary.parse_task(contract)
    fixed_task(task)
    expression = rotary.reference_expression(256, 128, ["x", "cosine", "sine"])
    expected = ast.parse("import torch\ndef reference(x, cosine, sine):\n    return " + expression + "\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-rotary-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-rotary-reference", "complete closed reshape/select/stack RoPE reference required")
    translation = Reader(source, task).read()
    if translation.readback().encode() != source.encode():
        raise Refusal("ptx-rotary-readback", "complete source readback differs")
    return task, translation
