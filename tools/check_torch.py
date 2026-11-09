#!/usr/bin/env python3
"""Optional CPU numerical evidence for the shipped reference formalizations."""

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


def main():
    import torch

    root = Path(__file__).resolve().parent.parent
    for p in sorted((root / "examples").iterdir()):
        task = Task.read(p / "task.json")
        source = (p / "reference.py").read_text()
        spec = read_spec(source, task)
        # Only the repository's own shipped examples are executed by this optional tool.
        env = {}
        exec(compile(source, str(p / "reference.py"), "exec"), env)
        for seed in range(16):
            exact, tensors = {}, []
            for b, buf in enumerate(task.buffers):
                if buf.role == "input":
                    values = [
                        Fraction(((seed + 1) * (i + 3) + b * 7) % 19 - 9, 4)
                        for i in range(buf.size)
                    ]
                    exact[b] = values
                    tensors.append(
                        torch.tensor([float(v) for v in values], dtype=torch.float32).reshape(
                            buf.shape
                        )
                    )
            expected = torch.tensor([float(evaluate(v, exact)) for v in spec], dtype=torch.float32)
            result = env["reference"](*tensors)
            result = result if isinstance(result, tuple) else (result,)
            actual = torch.cat([t.reshape(-1) for t in result])
            torch.testing.assert_close(actual, expected, rtol=1e-6, atol=1e-6)
        print(f"{p.name}: 16 CPU PyTorch comparisons passed", flush=True)


if __name__ == "__main__":
    main()
