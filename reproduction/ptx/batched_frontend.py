"""Lossless reader for the unchanged compiled batched GEMM development input.

This is source/contract preparation. It issues no certificate and establishes no
kernel, launch, reference or race theorem.
"""

import ast

from lark_kernels import matrix, ptx_matrix
from lark_kernels.ir import Refusal


def prepare(source, reference, contract):
    task = matrix.parse_task(contract)
    if (task.language != "cuda"
            or [buffer.name for buffer in task.buffers] != ["a", "b", "out"]
            or [buffer.shape for buffer in task.buffers]
            != [(32, 64, 256), (32, 256, 512), (32, 64, 512)]
            or [buffer.dtype for buffer in task.buffers] != ["float16"] * 3
            or (task.grid, task.block, task.warp) != (1048576, 1, 32)
            or task.fuel != (1030, 1, 1, 1)
            or any(type(v) is not int for v in (task.grid, task.block, task.warp, *task.fuel))):
        raise Refusal("ptx-batched-contract", "unchanged 32-batch full-size FP16 CUDA contract required")
    expected = ast.parse("import torch\ndef reference(a, b):\n    return (a.float() @ b.float()).half()\n")
    try:
        actual = ast.parse(reference)
    except SyntaxError as error:
        raise Refusal("ptx-batched-reference", "invalid reference syntax") from error
    if ast.dump(actual) != ast.dump(expected):
        raise Refusal("ptx-batched-reference", "complete closed batched matrix-multiply reference required")
    translation = ptx_matrix.Reader(source, task).read()
    if translation.readback().encode() != source.encode():
        raise Refusal("ptx-batched-readback", "complete source readback differs")
    return task, translation
