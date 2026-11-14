"""Parse and bind the two complete compiled FFN stages to their Lean proof.

Parsing alone establishes no correctness. The separate certificate checker
freshly compiles the owned libraries and the Main produced here. The original
shapes, launch geometry, FP16 intermediate and CUDA fuel remain fixed.
"""

import ast
from dataclasses import replace
import json

from . import matrix, ptx_matrix
from .ir import Refusal


CONTRACTS = {
    "up": (("x", "w1", "hidden"), ((64, 256), (256, 1024), (64, 1024)),
           65536, (1030, 1, 1, 1)),
    "down": (("hidden", "down", "out"), ((64, 1024), (1024, 256), (64, 256)),
             16384, (4102, 1, 1, 1)),
}
PROFILE = "source-bound-compiled-ffn-fp16-v1"
TAGS = ("original_reference", "exact_up", "exact_down", "complete_pipeline")

# Preserve both FP16 round trips and the independently supplied Torch operation
# order. The independent Lean tensor interpreter interprets these constructors;
# recognizing this data alone is not a correctness theorem.
REFERENCE = ["toHalf", ["matmul",
    ["fromHalf", ["toHalf", ["relu", ["matmul",
        ["fromHalf", ["input", 0]], ["fromHalf", ["input", 1]]]]]],
    ["fromHalf", ["input", 2]]]]


def fixed_task(task, stage):
    if stage not in CONTRACTS:
        raise Refusal("ptx-ffn-contract", "up or down stage required")
    names, shapes, grid, fuel = CONTRACTS[stage]
    if (task.language != "cuda"
            or task.entry != f"ffn_{stage}_cuda_64_256_1024_256"
            or tuple(b.name for b in task.buffers) != names
            or tuple(b.shape for b in task.buffers) != shapes
            or [b.dtype for b in task.buffers] != ["float16"] * 3
            or (task.grid, task.block, task.warp) != (grid, 1, 32)
            or tuple(task.fuel) != fuel
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-ffn-contract", "unchanged full-size FP16 " + stage + " contract required")


def reference_body(reference):
    expected = ast.parse("import torch\n\ndef reference(x, w1, down):\n"
                         "    return ((x.float() @ w1.float()).relu().half().float()"
                         " @ down.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-ffn-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-ffn-reference", "complete two-matmul/ReLU/FP16-intermediate reference required")
    return json.loads(json.dumps(REFERENCE))


def lean_reference(body):
    try:
        encoded = json.dumps(body, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise Refusal("ptx-ffn-reference", "a closed JSON tensor reference AST is required") from error
    if encoded != json.dumps(REFERENCE, separators=(",", ":")):
        raise Refusal("ptx-ffn-reference", "the complete FFN reference AST is required")

    def render(node):
        tag, *args = node
        if tag == "input":
            return f"(.input {args[0]})"
        return "(." + tag + " " + " ".join(render(a) for a in args) + ")"

    return render(body)


def prepare(up_source, down_source, reference, up_contract, down_contract):
    tasks = matrix.parse_task(up_contract), matrix.parse_task(down_contract)
    translations = []
    for stage, task, source in zip(("up", "down"), tasks, (up_source, down_source)):
        fixed_task(task, stage)
        parsed = ptx_matrix.Reader(source, task).read()
        if parsed.readback().encode() != source.encode():
            raise Refusal("ptx-ffn-readback", "complete " + stage + " source readback differs")
        translations.append(parsed)
    if replace(tasks[0].buffers[2], role="input") != tasks[1].buffers[0]:
        raise Refusal("ptx-ffn-contract", "the same complete FP16 intermediate must connect both stages")
    body = reference_body(reference)
    return tasks, translations, body


def render(tasks, translations, body):
    """Render only closed constructors; captured reference/Python is never code."""
    if len(tasks) != 2 or len(translations) != 2:
        raise Refusal("ptx-ffn-contract", "both original launch stages required")
    for stage, task in zip(("up", "down"), tasks, strict=True):
        fixed_task(task, stage)
    reference = lean_reference(body)
    return """import Lark.PtxFeedForwardPipeline
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkPtxFfnCertificate
open LarkNonlinear LarkPtxMatrix LarkPtxFeedForward
def up : List LarkPtxMatrix.Instruction := """ + translations[0].lean_program() + """
def down : List LarkPtxMatrix.Instruction := """ + translations[1].lean_program() + """
def originalReference : Reference.TensorReference := """ + reference + """
theorem original_reference : originalReference = Reference.referenceBody := by rfl
theorem exact_up : up = FfnUp.program := by decide
theorem exact_down : down = FfnDown.program := by decide
theorem complete_pipeline (ops : Ops α) :
    originalReference = Reference.referenceBody ∧ Pipeline.Correct ops up down := by
  constructor
  · exact original_reference
  · rw [exact_up, exact_down]
    exact Pipeline.kernel_correct ops
#print axioms original_reference
#print axioms exact_up
#print axioms exact_down
#print axioms complete_pipeline
end LarkPtxFfnCertificate
"""
