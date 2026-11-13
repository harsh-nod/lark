"""Lossless data reader for the complete unchanged compiled FP16 GEMM profile.

It extends the published GEMV grammar without changing that reader or its proofs.
The companion certificate module checks the source-bound development profile.
"""

import ast
import json
from dataclasses import dataclass

from . import matrix, ptx_dot
from .ir import Refusal


NEW_OPERATIONS = {
    "shr.s32": "shiftRightSigned32", "shr.u32": "shiftRightUnsigned32",
    "and.b32": "andBits32", "sub.s32": "subSigned32", "mul.wide.u32": "mulWideUnsigned32",
}


def lean_instruction(instruction):
    if not isinstance(instruction, (list, tuple)) or not instruction or type(instruction[0]) is not str:
        raise Refusal("ptx-matrix-constructor", "typed instruction data required")
    tag, *args = instruction
    if tag not in NEW_OPERATIONS.values():
        return "(.base " + ptx_dot.lean_instruction(instruction) + ")"
    if len(args) != 3 or any(type(x) is not int or not 0 <= x < 256 for x in args[:2]):
        raise Refusal("ptx-matrix-constructor", "typed register operands required")
    value = args[2]
    if tag in {"andBits32", "subSigned32"}:
        if (not isinstance(value, (list, tuple)) or len(value) != 2
                or type(value[0]) is not str or value[0] not in {"reg", "imm"}
                or type(value[1]) is not int
                or not (0 <= value[1] < 256 if value[0] == "reg" else -(2**31) <= value[1] < 2**31)):
            raise Refusal("ptx-matrix-constructor", "typed 32-bit operand required")
        last = f"(.{value[0]} ({value[1]}))"
    else:
        if type(value) is not int or not 0 <= value < 2**32:
            raise Refusal("ptx-matrix-constructor", "unsigned 32-bit immediate required")
        last = str(value)
    return f"(.{tag} {args[0]} {args[1]} {last})"


@dataclass
class Translation(ptx_dot.Translation):
    def lean_program(self):
        return "[" + ", ".join(lean_instruction(ins) for ins in self.instructions) + "]"


class Reader(ptx_dot.Reader):
    def instruction(self):
        op = self.peek()
        if op not in NEW_OPERATIONS:
            return super().instruction()
        self.pop()
        dest = self.reg("i64" if op == "mul.wide.u32" else "i32")
        self.comma()
        left = self.reg("i32")
        self.comma()
        value = self.operand("i32") if op in {"and.b32", "sub.s32"} else self.integer(signed=False)
        self.pop(";")
        self.code.append([NEW_OPERATIONS[op], dest, left, value])
        if len(self.code) > 256:
            raise Refusal("ptx-matrix-capacity", "at most 256 source instructions")

    def read(self):
        parsed = super().read()
        return Translation(**vars(parsed))


def translate(source, contract):
    task = matrix.parse_task(contract)
    if (task.language != "cuda" or task.warp != 32 or task.block != 1
            or [b.shape for b in task.buffers] != [(64, 256), (256, 512), (64, 512)]
            or [b.name for b in task.buffers] != ["a", "b", "out"]):
        raise Refusal("ptx-matrix-contract", "unchanged 64x256 times 256x512 FP16 CUDA contract required")
    parsed = Reader(source, task).read()
    if parsed.readback().encode() != source.encode():
        raise Refusal("ptx-matrix-readback", "complete source readback differs")
    return task, parsed


def prepare(source, reference, contract):
    task, parsed = translate(source, contract)
    expected = ast.parse("import torch\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-matrix-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-matrix-reference", "complete closed FP16 matrix-multiply reference required")
    return task, parsed


PROFILE = "source-bound-compiled-gemm-fp16-v1"
TAGS = ptx_dot.TAGS
REFERENCE = ptx_dot.REFERENCE


def prepare_certificate(source, reference, contract):
    task, translation = prepare(source, reference, contract)
    return task, translation, json.loads(json.dumps(REFERENCE))


def lean_reference(body):
    return ptx_dot.lean_reference(body)


def render(task, translation, reference_body):
    if ([buffer.shape for buffer in task.buffers] != [(64, 256), (256, 512), (64, 512)]
            or [buffer.dtype for buffer in task.buffers] != ["float16"] * 3
            or (task.grid, task.block, task.warp) != (32768, 1, 32)
            or tuple(task.fuel) != (1030, 1, 1, 1)
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-matrix-contract", "fixed GEMM shape, dtype, geometry or CUDA fuel differs")
    return f"""import Lark.PtxMatrix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxMatrixCertificate
open LarkNonlinear
def program : List LarkPtxMatrix.Instruction := {translation.lean_program()}
def referenceBody : LarkPtxMatrix.Gemm.TensorReference := {lean_reference(reference_body)}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (LarkPtxMatrix.Gemm.evaluateReference ops input referenceBody).getD []
theorem source_program : program = LarkPtxMatrix.Gemm.program := by decide
theorem reference_body : referenceBody = LarkPtxMatrix.Gemm.referenceBody := by rfl
theorem launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPtxMatrix.Gemm.LaneSequence ops program 0 32768
      (initial LarkPtxMatrix.Gemm.layout input outside)
      (LarkPtxMatrix.Gemm.finalState ops input outside) := by
  rw [source_program]
  exact LarkPtxMatrix.Gemm.launch_execution ops input outside
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree LarkPtxMatrix.Gemm.geometry
      (LarkPtxMatrix.Gemm.finalState ops input outside).trace = true :=
  LarkPtxMatrix.Gemm.launch_raceFree ops input outside
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract LarkPtxMatrix.Gemm.layout (LarkPtxMatrix.Gemm.finalState ops input outside) =
      some (spec ops input) := by
  unfold spec
  rw [reference_body, LarkPtxMatrix.Gemm.evaluate_reference_body]
  simp only [Option.getD_some]
  exact LarkPtxMatrix.Gemm.final_extract ops input outside
theorem kernel_eq_spec (ops : Ops α) : LarkPtxMatrix.Gemm.Correct ops program (spec ops) := by
  intro input outside
  exact ⟨LarkPtxMatrix.Gemm.finalState ops input outside, launch ops input outside,
    race_free ops input outside, segment_equivalence ops input outside,
    LarkPtxMatrix.Gemm.launch_other_memory ops input outside⟩
""" + "".join("#print axioms LarkPtxMatrixCertificate." + tag + "\n" for tag in TAGS) + (
        "end LarkPtxMatrixCertificate\n")
