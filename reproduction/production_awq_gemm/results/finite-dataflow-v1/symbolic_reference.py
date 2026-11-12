"""Dense source-order expression reference, independent of native indexing.

Each K16 matrix instruction adds its fresh dot sum to the prior accumulator.
No native lane, block decode, shared stride or parsed instruction is consulted.
This finite expression check is separate from a dense-real equality proof.
"""

import hashlib
import json

from lark_kernels.ir import Node, literal, node


def output_expression(m, k, n, row, col):
    assert 0 <= row < m and 0 <= col < n and k % 16 == 0
    acc = literal(0)
    for tile in range(k//16):
        dot = literal(0)
        for component in range(16):
            j = tile*16+component
            a = node("un", "fromHalf", node("input", 0, row*k+j))
            b = node("un", "fromHalf", node("input", 1, j*n+col))
            dot = node("bin", "add", dot, node("bin", "mul", a, b))
        acc = node("bin", "add", dot, acc)
    return node("un", "toHalf", acc)


def expression_hashes(values):
    # Memoize identities rather than recursively hashing entire dataclass
    # keys. The digest depends only on expression contents, not DAG sharing.
    memo = {}

    def digest(value):
        key = id(value)
        if key not in memo:
            children = [digest(arg) if isinstance(arg, Node) else arg for arg in value.args]
            payload = json.dumps([value.op, children], separators=(",", ":")).encode()
            memo[key] = hashlib.sha256(payload).hexdigest()
        return memo[key]

    return [digest(value) for value in values]
