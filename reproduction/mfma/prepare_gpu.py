"""Generate ordinary row-major MFMA basis pairs and exactly representable tiles."""

import argparse
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import random
import shutil
import struct
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from lark_kernels.ir import Task
from lark_kernels.spec import read_spec

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def evaluate(n, inputs):
    if n.op == "input":
        return inputs[n.args[0]][n.args[1]]
    if n.op == "lit":
        return n.args[0] / n.args[1]
    if n.op == "un" and n.args[0] == "fromHalf":
        return evaluate(n.args[1], inputs)
    if n.op == "bin" and n.args[0] in {"add", "mul"}:
        a, b = evaluate(n.args[1], inputs), evaluate(n.args[2], inputs)
        return a + b if n.args[0] == "add" else a * b
    raise ValueError("Unexpected independent reference operation")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    case = ROOT / "cases/gemm16"
    shutil.copytree(case, out / "cases/gemm16")
    for name in ("driver.hip", "run_gpu.py"):
        shutil.copyfile(ROOT / name, out / name)
    task = Task.read(case / "task.json")
    spec = read_spec((case / "reference.py").read_text(), task)
    gen = random.Random(261102028)
    checked, trials = 0, 0
    with ExitStack() as stack:
        files = [
            stack.enter_context((out / n).open("wb"))
            for n in ("a.bin", "b.bin", "c.bin", "expected.bin")
        ]

        def emit(a, b, c, d, check=False):
            nonlocal checked, trials
            if check:
                actual = [evaluate(n, (a, b, c)) for n in spec]
                if actual != d:
                    raise ValueError("Independent AST reference differs from generated expectation")
                checked += 1
            for f, values, kind in zip(files, (a, b, c, d), ("e", "e", "f", "f")):
                f.write(struct.pack("<" + kind * 256, *values))
            trials += 1

        zero = [0.0] * 256
        for ai in range(256):
            row, ka = divmod(ai, 16)
            a = zero.copy()
            a[ai] = 1.0
            for bi in range(256):
                kb, col = divmod(bi, 16)
                b, d = zero.copy(), zero.copy()
                b[bi] = 1.0
                if ka == kb:
                    d[row * 16 + col] = 1.0
                emit(a, b, zero, d, check=(ai * 256 + bi) % 4096 == 0)
        for ci in range(256):
            c = zero.copy()
            c[ci] = 1.0
            emit(zero, zero, c, c, check=True)
        for trial in range(32):
            divisor = 1 if trial < 16 else 16
            a = [gen.randint(-3, 3) / divisor for _ in range(256)]
            b = [gen.randint(-3, 3) / divisor for _ in range(256)]
            c = [gen.randint(-4, 4) / divisor for _ in range(256)]
            d = [
                sum(a[i * 16 + k] * b[k * 16 + j] for k in range(16)) + c[i * 16 + j]
                for i in range(16)
                for j in range(16)
            ]
            emit(a, b, c, d, check=True)
    report = {
        "schema": 1,
        "experiment": "exact-source-full-wave-mfma-tile",
        "seed": 261102028,
        "trials": trials,
        "basis_pairs": 65536,
        "accumulator_basis": 256,
        "exact_random_tiles": 32,
        "comparisons": trials * 256,
        "independent_ast_reference_checks": checked,
        "model_calls": 0,
        "generator_sha256": sha(Path(__file__)),
        "scope": "Same source file as the single-wave 16x16 certificate. Every launch uses grid=1, block=64 and separately guarded tile pointers. Exhaustive A/B basis pairs, accumulator basis and exactly representable small integer/dyadic random operands. Finite native MFMA conformance; not full IEEE semantics, other shapes/modifiers, original production kernels or NVIDIA evidence.",
        "files": {str(f.relative_to(out)): sha(f) for f in sorted(out.rglob("*")) if f.is_file()},
    }
    (out / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"files", "scope"}}))


if __name__ == "__main__":
    main()
