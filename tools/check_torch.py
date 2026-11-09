#!/usr/bin/env python3
"""Optional CPU numerical evidence for example and reduced-study references."""

from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from lark_kernels.ir import Task
from lark_kernels.spec import read_spec


def evaluate(expr, inputs):
    op, args = expr.op, expr.args
    if op == "input":
        return inputs[args[0]][args[1]]
    if op == "lit":
        return Fraction(*args)
    kind, a, b = args
    x, y = evaluate(a, inputs), evaluate(b, inputs)
    return {
        "add": lambda: x + y,
        "sub": lambda: x - y,
        "mul": lambda: x * y,
        "max": lambda: max(x, y),
    }[kind]()


def check_reference(torch, task, source, filename):
    spec = read_spec(source, task)
    # Only references shipped or declared by this repository are executed here.
    env = {}
    exec(compile(source, str(filename), "exec"), env)
    for seed in range(16):
        exact, tensors = {}, []
        for b, buf in enumerate(task.buffers):
            if buf.role == "input":
                values = [
                    Fraction(((seed + 1) * (i + 3) + b * 7) % 19 - 9, 4) for i in range(buf.size)
                ]
                exact[b] = values
                tensors.append(
                    torch.tensor([float(v) for v in values], dtype=torch.float32).reshape(buf.shape)
                )
        expected = torch.tensor([float(evaluate(v, exact)) for v in spec], dtype=torch.float32)
        result = env["reference"](*tensors)
        result = result if isinstance(result, tuple) else (result,)
        actual = torch.cat([t.reshape(-1) for t in result])
        torch.testing.assert_close(actual, expected, rtol=1e-6, atol=1e-6)


def main():
    import torch

    root = Path(__file__).resolve().parent.parent
    cases = sorted((root / "examples").iterdir()) + sorted(
        (root / "reproduction" / "cases").iterdir()
    )
    for p in cases:
        task = Task.read(p / "task.json")
        source = (p / "reference.py").read_text()
        check_reference(torch, task, source, p / "reference.py")
        print(f"{p.name}: 16 CPU PyTorch comparisons passed", flush=True)
    # Exercise spatial/batch/group indexing and trailing-dimension broadcasting
    # beyond the deliberately tiny proof fixtures.
    import json

    for name, shapes, output, expression in (
        ("broadcast", [[2, 1, 3], [1, 4, 1]], [2, 4, 3], "a + b"),
        ("bmm", [[2, 3, 4], [2, 4, 5]], [2, 3, 5], "torch.bmm(a, b)"),
        ("spatial-conv", [[2, 4, 4, 5], [6, 4, 2, 3]], [2, 6, 3, 3], "torch.conv2d(a, b)"),
        (
            "grouped-conv",
            [[2, 4, 4, 5], [6, 2, 2, 3]],
            [2, 6, 3, 3],
            "torch.conv2d(a, b, groups=2)",
        ),
    ):
        data = {
            "name": name,
            "entry": "unused",
            "language": "hip",
            "launch": {"grid": 1, "block": 1},
            "buffers": [
                {"name": n, "role": "input", "shape": s, "dtype": "float32"}
                for n, s in zip(("a", "b"), shapes)
            ]
            + [{"name": "out", "role": "output", "shape": output, "dtype": "float32"}],
        }
        task = Task.parse(json.dumps(data))
        source = "import torch\ndef reference(a,b):\n return " + expression + "\n"
        check_reference(torch, task, source, name)
        print(f"{name}: 16 CPU PyTorch comparisons passed", flush=True)


if __name__ == "__main__":
    main()
