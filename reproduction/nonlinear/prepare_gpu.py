"""Prepare independent CPU PyTorch values for exact certified-source GPU checks."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import struct
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec
from reproduction.nonlinear.gpu_bundle import wrapper_source

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def f32(v):
    return struct.unpack("<f", struct.pack("<f", v))[0]


def f16(v):
    return struct.unpack("<e", struct.pack("<e", f32(v)))[0]


def evaluate(n, inputs):
    a = n.args
    if n.op == "input":
        return inputs[a[0]][a[1]]
    if n.op == "lit":
        return f32(a[0] / a[1])
    if n.op == "un":
        x = evaluate(a[1], inputs)
        return {
            "exp": lambda: f32(math.exp(x)),
            "tanh": lambda: f32(math.tanh(x)),
            "rsqrt": lambda: f32(1 / math.sqrt(x)),
            "fromHalf": lambda: x,
            "toHalf": lambda: f16(x),
        }[a[0]]()
    kind, x, y = a
    x, y = evaluate(x, inputs), evaluate(y, inputs)
    return f32(
        {
            "add": lambda: x + y,
            "sub": lambda: x - y,
            "mul": lambda: x * y,
            "div": lambda: x / y,
            "max": lambda: max(x, y),
        }[kind]()
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    import torch

    torch.set_num_threads(1)
    dataset = {
        "schema": 1,
        "reference": "CPU PyTorch " + torch.__version__,
        "cases": [],
        "seed": 261102028,
        "trials": "6 normal(0,.25) trials plus zeros, .125, alternating signs, small uniform",
        "runner_sha256": sha(Path(__file__)),
    }
    for case in sorted((ROOT / "cases").glob("*/*")):
        t = Task.read(case / "task.json")
        env = {}
        source = (case / "reference.py").read_text()
        exec(compile(source, str(case / "reference.py"), "exec"), env)
        spec = read_spec(source, t)
        row = {
            "key": case.parent.name + "/" + case.name,
            "task": case.name,
            "dtype": case.parent.name,
            "source_sha256": sha(case / "kernel.hip"),
            "reference_sha256": sha(case / "reference.py"),
            "task_sha256": sha(case / "task.json"),
            "source_text": (case / "kernel.hip").read_text(),
            "reference_text": source,
            "task_text": (case / "task.json").read_text(),
            "trials": [],
            "rtol": 0.01 if case.parent.name == "float16" else 2e-5,
            "atol": 0.01 if case.parent.name == "float16" else 2e-6,
        }
        for trial in range(10):
            rng = random.Random(dataset["seed"] + trial)
            buffers = []
            inputs = []
            exact = {}
            for b, buf in enumerate(t.buffers):
                values = None
                if buf.role == "input":
                    if trial < 6:
                        values = [rng.gauss(0, 0.25) for _ in range(buf.size)]
                    elif trial == 6:
                        values = [0.0] * buf.size
                    elif trial == 7:
                        values = [0.125] * buf.size
                    elif trial == 8:
                        values = [0.125 if i % 2 else -0.125 for i in range(buf.size)]
                    else:
                        values = [rng.uniform(-0.001, 0.001) for _ in range(buf.size)]
                    cast = f16 if buf.dtype == "float16" else f32
                    values = [cast(v) for v in values]
                    exact[b] = values
                    inputs.append(
                        torch.tensor(
                            values, dtype=torch.float16 if buf.dtype == "float16" else torch.float32
                        ).reshape(buf.shape)
                    )
                buffers.append(
                    {"role": buf.role, "dtype": buf.dtype, "size": buf.size, "values": values}
                )
            expected = env["reference"](*inputs).reshape(-1).tolist()
            modeled = [evaluate(v, exact) for v in spec]
            torch.testing.assert_close(
                torch.tensor(modeled), torch.tensor(expected), rtol=row["rtol"], atol=row["atol"]
            )
            row["trials"].append(
                {
                    "trial": trial,
                    "buffers": buffers,
                    "expected": expected,
                    "cpu_spec_max_abs_error": max(abs(a - b) for a, b in zip(expected, modeled)),
                }
            )
        dataset["cases"].append(row)
        print(row["key"], "10 CPU spec comparisons passed", flush=True)
    wrapper = wrapper_source(dataset["cases"])
    (args.output / "certified.hip").write_text(wrapper)
    dataset["wrapper_sha256"] = sha(args.output / "certified.hip")
    (args.output / "cases.json").write_text(json.dumps(dataset, indent=2) + "\n")


if __name__ == "__main__":
    main()
