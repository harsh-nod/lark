"""Lossless reader and source-bound input for original compiled FP16 Linear.

The complete matrix-plus-bias contract and reference cast order are fixed.
The complete179instruction proof remains a separate development profile; it
adds no legacy registration, original optimized kernel or model-cohort success.
"""

import ast
import json
from dataclasses import dataclass

from . import linear, ptx_matrix
from .ir import Refusal


PROFILE = "source-bound-compiled-linear-fp16-v1"
TAGS = ptx_matrix.TAGS
REFERENCE = ["toHalf", ["add", ["matmul", ["fromHalf", ["input", 0]],
                            ["fromHalf", ["input", 1]]], ["fromHalf", ["input", 2]]]]


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


def fixed_task(task):
    if (task.language != "cuda"
            or [b.name for b in task.buffers] != ["a", "b", "bias", "out"]
            or [b.shape for b in task.buffers] != [(64, 256), (256, 512), (512,), (64, 512)]
            or [b.dtype for b in task.buffers] != ["float16"] * 4
            or (task.grid, task.block, task.warp) != (32768, 1, 32)
            or tuple(task.fuel) != (1030, 1, 1, 1)
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-linear-contract", "unchanged full-size FP16 matrix multiply plus bias required")


def prepare(source, reference, contract):
    task = linear.parse_task(contract)
    fixed_task(task)
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


def prepare_certificate(source, reference, contract):
    task, translation = prepare(source, reference, contract)
    return task, translation, json.loads(json.dumps(REFERENCE))


def lean_reference(body):
    try:
        encoded = json.dumps(body, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise Refusal("ptx-linear-reference", "a closed JSON tensor reference AST is required") from error
    if encoded != json.dumps(REFERENCE, separators=(",", ":")):
        raise Refusal("ptx-linear-reference", "unsupported closed tensor reference AST")
    return "(.toHalf (.add (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))) (.fromHalf (.input 2))))"


def render(task, translation, reference_body):
    fixed_task(task)
    reference = lean_reference(reference_body)
    return f"""import Lark.PtxLinearLaunch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxLinearCertificate
open LarkNonlinear
def program : List LarkPtxLinear.Instruction := {translation.lean_program()}
def referenceBody : LarkPtxLinear.Linear.Launch.TensorReference := {reference}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkPtxLinear.Linear.Launch.referenceSpec ops input
theorem source_program : program = LarkPtxLinear.Linear.program := by decide
theorem reference_body : referenceBody = LarkPtxLinear.Linear.Launch.referenceBody := by rfl
theorem reference_denotation (ops : Ops α) (input : Nat → Nat → α) :
    LarkPtxLinear.Linear.Launch.evaluateReference ops input referenceBody = some (spec ops input) := by
  rw [reference_body]
  exact LarkPtxLinear.Linear.Launch.evaluate_reference_body ops input
theorem kernel_eq_spec (ops : Ops α) :
    LarkPtxLinear.Linear.Launch.Correct ops program (spec ops) := by
  rw [source_program]
  exact LarkPtxLinear.Linear.Launch.kernel_correct ops
theorem launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LarkPtxLinear.Linear.Launch.LaneSequence ops program 0 32768
      (initial LarkPtxLinear.Linear.layout input outside) final ∧
    raceFree LarkPtxLinear.Linear.geometry final.trace = true ∧
    extract LarkPtxLinear.Linear.layout final = some (spec ops input) ∧
    (∀ l, (∀ i, i < 32768 → l ≠ LarkPtxLinear.Linear.Exit.outputCell i) →
      final.memory l = (initial LarkPtxLinear.Linear.layout input outside).memory l) :=
  kernel_eq_spec ops input outside
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LarkPtxLinear.Linear.Launch.LaneSequence ops program 0 32768
      (initial LarkPtxLinear.Linear.layout input outside) final ∧
      raceFree LarkPtxLinear.Linear.geometry final.trace = true := by
  obtain ⟨final, execution, race, values, preserved⟩ := launch ops input outside
  exact ⟨final, execution, race⟩
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    ∃ final, LarkPtxLinear.Linear.Launch.LaneSequence ops program 0 32768
      (initial LarkPtxLinear.Linear.layout input outside) final ∧
      extract LarkPtxLinear.Linear.layout final =
        LarkPtxLinear.Linear.Launch.evaluateReference ops input referenceBody := by
  obtain ⟨final, execution, race, values, preserved⟩ := launch ops input outside
  exact ⟨final, execution, values.trans (reference_denotation ops input).symm⟩
""" + "".join("#print axioms LarkPtxLinearCertificate." + tag + "\n" for tag in TAGS) + (
        "end LarkPtxLinearCertificate\n")
