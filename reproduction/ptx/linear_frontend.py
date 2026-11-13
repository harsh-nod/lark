"""Lossless preparation for unchanged compiled FP16 matrix multiply plus bias.

This adds data constructors for the actual conversion and shift instructions.
It is not a kernel certificate; their formal execution and the complete source
launch, reference and race proofs are still required.
"""

import ast
from dataclasses import dataclass

from lark_kernels import linear, ptx_matrix
from lark_kernels.ir import Refusal


def lean_instruction(instruction):
    if not isinstance(instruction, (list, tuple)) or not instruction or type(instruction[0]) is not str:
        raise Refusal("ptx-linear-constructor", "typed instruction data required")
    tag, *args = instruction
    if tag not in {"signExtend32", "shiftLeft64"}:
        return "(.base " + ptx_matrix.lean_instruction(instruction) + ")"
    if len(args) != (2 if tag == "signExtend32" else 3) or any(
            type(v) is not int or not 0 <= v < 256 for v in args[:2]):
        raise Refusal("ptx-linear-constructor", "typed register operands required")
    if tag == "signExtend32":
        return f"(.signExtend32 {args[0]} {args[1]})"
    if type(args[2]) is not int or not 0 <= args[2] < 2**32:
        raise Refusal("ptx-linear-constructor", "unsigned shift immediate required")
    return f"(.shiftLeft64 {args[0]} {args[1]} {args[2]})"


@dataclass
class Translation(ptx_matrix.Translation):
    def lean_program(self):
        return "[" + ", ".join(lean_instruction(ins) for ins in self.instructions) + "]"


class Reader(ptx_matrix.Reader):
    def instruction(self):
        op = self.peek()
        if op not in {"cvt.s64.s32", "shl.b64"}:
            return super().instruction()
        self.pop()
        destination = self.reg("i64")
        self.comma()
        source = self.reg("i32" if op == "cvt.s64.s32" else "i64")
        if op == "cvt.s64.s32":
            instruction = ["signExtend32", destination, source]
        else:
            self.comma()
            instruction = ["shiftLeft64", destination, source, self.integer(signed=False)]
        self.pop(";")
        self.code.append(instruction)
        if len(self.code) > 256:
            raise Refusal("ptx-linear-capacity", "at most 256 source instructions")

    def read(self):
        return Translation(**vars(super().read()))


def prepare(source, reference, contract):
    task = linear.parse_task(contract)
    if (task.language != "cuda"
            or [b.name for b in task.buffers] != ["a", "b", "bias", "out"]
            or [b.shape for b in task.buffers] != [(64, 256), (256, 512), (512,), (64, 512)]
            or [b.dtype for b in task.buffers] != ["float16"] * 4
            or (task.grid, task.block, task.warp) != (32768, 1, 32)
            or tuple(task.fuel) != (1030, 1, 1, 1)
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-linear-contract", "unchanged full-size FP16 matrix multiply plus bias required")
    expected = ast.parse("import torch\ndef reference(a, b, bias):\n"
                         "    return (a.float() @ b.float() + bias.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-linear-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-linear-reference", "complete closed matrix-plus-bias reference required")
    translation = Reader(source, task).read()
    if translation.readback().encode() != source.encode():
        raise Refusal("ptx-linear-readback", "complete source readback differs")
    return task, translation
