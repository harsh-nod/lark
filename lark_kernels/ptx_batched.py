"""Lossless reader and source-bound checker input for full-size compiled BMM.

The complete original 32-batch FP16 task is fixed. The certificate remains a
separate development profile and adds no legacy model-cohort success.
"""

import ast
import json

from . import matrix, ptx_matrix
from .ir import Refusal

PROFILE = "source-bound-compiled-bmm-fp16-v1"
TAGS = ptx_matrix.TAGS
REFERENCE = ptx_matrix.REFERENCE


def fixed_task(task):
    if (task.language != "cuda"
            or [b.name for b in task.buffers] != ["a", "b", "out"]
            or [b.shape for b in task.buffers]
            != [(32, 64, 256), (32, 256, 512), (32, 64, 512)]
            or [b.dtype for b in task.buffers] != ["float16"] * 3
            or (task.grid, task.block, task.warp) != (1048576, 1, 32)
            or tuple(task.fuel) != (1030, 1, 1, 1)
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-batched-contract", "unchanged 32-batch full-size FP16 CUDA contract required")


def translate(source, contract):
    task = matrix.parse_task(contract)
    fixed_task(task)
    translation = ptx_matrix.Reader(source, task).read()
    if translation.readback().encode() != source.encode():
        raise Refusal("ptx-batched-readback", "complete source readback differs")
    return task, translation


def prepare(source, reference, contract):
    task, translation = translate(source, contract)
    expected = ast.parse("import torch\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-batched-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-batched-reference", "complete closed batched matrix-multiply reference required")
    return task, translation


def prepare_certificate(source, reference, contract):
    task, translation = prepare(source, reference, contract)
    return task, translation, json.loads(json.dumps(REFERENCE))


def render(task, translation, reference_body):
    fixed_task(task)
    reference = ptx_matrix.lean_reference(reference_body)
    return f"""import Lark.PtxBatchedBody
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxBatchedCertificate
open LarkNonlinear
def program : List LarkPtxMatrix.Instruction := {translation.lean_program()}
def referenceBody : LarkPtxBatched.Bmm.Body.TensorReference := {reference}
def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  LarkPtxBatched.Bmm.Body.referenceSpec ops input
theorem source_program : program = LarkPtxBatched.Bmm.program := by decide
theorem reference_body : referenceBody = LarkPtxBatched.Bmm.Body.referenceBody := by rfl
theorem reference_denotation (ops : Ops α) (input : Nat → Nat → α) :
    LarkPtxBatched.Bmm.Body.evaluateReference ops input referenceBody = some (spec ops input) := by
  rw [reference_body]
  exact LarkPtxBatched.Bmm.Body.evaluate_reference_body ops input
theorem kernel_eq_spec (ops : Ops α) :
    LarkPtxBatched.Bmm.Body.Correct ops program (spec ops) := by
  rw [source_program]
  exact LarkPtxBatched.Bmm.Body.kernel_correct ops
theorem launch (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LarkPtxBatched.Bmm.Body.LaneSequence ops program 0 1048576
      (initial LarkPtxBatched.Bmm.layout input outside) final ∧
    raceFree LarkPtxBatched.Bmm.geometry final.trace = true ∧
    extract LarkPtxBatched.Bmm.layout final = some (spec ops input) ∧
    (∀ l, (∀ i, i < 1048576 → l ≠ LarkPtxBatched.Bmm.Body.outputCell i) →
      final.memory l = (initial LarkPtxBatched.Bmm.layout input outside).memory l) :=
  kernel_eq_spec ops input outside
theorem race_free (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∃ final, LarkPtxBatched.Bmm.Body.LaneSequence ops program 0 1048576
      (initial LarkPtxBatched.Bmm.layout input outside) final ∧
      raceFree LarkPtxBatched.Bmm.geometry final.trace = true := by
  obtain ⟨final, execution, race, values, preserved⟩ := launch ops input outside
  exact ⟨final, execution, race⟩
theorem segment_equivalence (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    ∃ final, LarkPtxBatched.Bmm.Body.LaneSequence ops program 0 1048576
      (initial LarkPtxBatched.Bmm.layout input outside) final ∧
      extract LarkPtxBatched.Bmm.layout final =
        LarkPtxBatched.Bmm.Body.evaluateReference ops input referenceBody := by
  obtain ⟨final, execution, race, values, preserved⟩ := launch ops input outside
  exact ⟨final, execution, values.trans (reference_denotation ops input).symm⟩
""" + "".join("#print axioms LarkPtxBatchedCertificate." + tag + "\n" for tag in TAGS) + (
        "end LarkPtxBatchedCertificate\n")
