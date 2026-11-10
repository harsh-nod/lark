"""Untrusted execution and expression checks; this does not issue a certificate."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_rmsnorm, partition_collective  # noqa: E402
from lark_kernels.ir import Refusal, node  # noqa: E402

CASE = Path(__file__).resolve().parent / "cases/weighted_16384"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def evaluate(source, reference, task_source):
    task = native_rmsnorm.parse_task(task_source)
    native_rmsnorm.check_reference(reference, task)
    tr = partition_collective.translate(source, task)
    machine = partition_collective.Machine(task, tr).run()
    categories = Counter()
    for access in machine.trace:
        t, (space, owner, buffer, offset), write, epoch = (
            access.thread,
            access.location,
            access.write,
            access.epoch,
        )
        if space == "global":
            if write:
                good = (
                    buffer == 0
                    and owner == 0
                    and t == offset // 16384 * 1024 + offset % 16384 // 8 % 1024
                )
                kind = "output"
            else:
                good, kind = buffer != 0 and owner == 0, "input"
        elif space == "shared" and buffer == 0:
            if write:
                good = (
                    owner == t // 1024
                    and offset == t % 1024 // 64
                    and t % 1024 % 64 == 0
                    and epoch[1] == 0
                )
                kind = "partial-store"
            else:
                good, kind = owner == t // 1024 and epoch[1] == 1, "partial-load"
        elif space == "shared" and buffer == 1:
            if write:
                good = owner == t // 1024 and offset == 0 and t % 1024 == 0 and epoch[1] == 1
                kind = "scale-store"
            else:
                good, kind = owner == t // 1024 and offset == 0 and epoch[1] == 2, "scale-load"
        else:
            good, kind = False, "unsupported"
        require(good, "access classification failed: " + str(access))
        categories[kind] += 1
    expected_scales = []
    for row in range(task.grid):
        scale = machine.memory[("shared", row, 1, 0)]
        require(scale.op == "un" and scale.args[0] == "rsqrt", "scale is not rsqrt")
        plus = scale.args[1]
        require(
            plus.op == "bin" and plus.args[0] == "add" and plus.args[2] == node("lit", 1, 100000),
            "epsilon differs",
        )
        mean = plus.args[1]
        require(
            mean.op == "bin" and mean.args[0] == "div" and mean.args[2] == node("lit", 16384, 1),
            "mean divisor differs",
        )
        memo = {}

        def squares(expr):
            if id(expr) in memo:
                return memo[id(expr)]
            if expr.op == "lit" and expr.args[0] == 0:
                result = Counter()
            elif expr.op == "bin" and expr.args[0] == "add":
                result = squares(expr.args[1]) + squares(expr.args[2])
            elif expr.op == "bin" and expr.args[0] == "mul" and expr.args[1] == expr.args[2]:
                value = expr.args[1]
                require(
                    value.op == "un" and value.args[0] == "fromHalf",
                    "square half conversion differs",
                )
                leaf = value.args[1]
                require(leaf.op == "input" and leaf.args[0] == 1, "square input buffer differs")
                result = Counter({leaf.args[1]: 1})
            else:
                raise ValueError("unexpected square-sum expression")
            memo[id(expr)] = result
            return result

        coefficients = squares(mean.args[1])
        require(
            coefficients == Counter({row * 16384 + c: 1 for c in range(16384)}),
            "square-sum coverage differs",
        )
        expected_scales.append(scale)
    actual = machine.outputs()
    require(len(actual) == task.grid * 16384, "output count differs")
    for offset, value in enumerate(actual):
        row, col = divmod(offset, 16384)
        wanted = node(
            "un",
            "toHalf",
            node(
                "bin",
                "mul",
                node(
                    "bin",
                    "mul",
                    node("un", "fromHalf", node("input", 1, offset)),
                    expected_scales[row],
                ),
                node("un", "fromHalf", node("input", 2, col)),
            ),
        )
        require(value == wanted, "output expression differs at " + str(offset))
    return {
        "instructions": len(tr.program),
        "accesses": len(machine.trace),
        "output_expressions_checked": len(actual),
        "squared_input_cells_checked": task.grid * 16384,
        "categories": dict(categories),
        "source_readback": tr.readback() == source,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source, reference, task = [
        (CASE / name).read_text() for name in ("kernel.hip", "reference.py", "task.json")
    ]
    start = time.monotonic()
    baseline = evaluate(source, reference, task)
    controls = []
    changes = {
        "duplicated-last-reduction-offset": (
            source.replace("__shfl_down(variance, 8, 16)", "__shfl_down(variance, 4, 16)"),
            "square-sum coverage differs",
        ),
        "wrong-weight-index": (
            source.replace("weight[outVector * 8 + outComponent]", "weight[0]"),
            "output expression differs",
        ),
        "unguarded-partial-store": (
            source.replace(
                "if (lane == 0) { partials[warp] = variance; }", "partials[warp] = variance;"
            ),
            "access classification failed",
        ),
        "missing-first-block-barrier": (source.replace("__syncthreads();", "", 1), "uninitialized"),
    }
    for name, (changed, expected) in changes.items():
        (out / (name + ".hip")).write_text(changed)
        try:
            evaluate(changed, reference, task)
        except (ValueError, Refusal) as error:
            require(expected in str(error), "wrong control refusal: " + str(error))
            (out / (name + ".log")).write_text(str(error) + "\n")
            controls.append({"name": name, "rejected": True, "gate": expected, "proof": False})
        else:
            raise RuntimeError("untrusted control accepted: " + name)
    write(
        out / "results.json",
        {
            "status": "untrusted-preflight-passed",
            "baseline": baseline,
            "controls": controls,
            "seconds": time.monotonic() - start,
            "full_kernel_proof": False,
            "source_trace_goodness_proved": False,
            "certificates": 0,
            "fresh_lean_checks": 0,
            "gpu_trials": 0,
            "model_calls": 0,
            "original_paper_fully_reproduced": False,
            "scope": "Development preflight of the actual 1,024-thread weighted 16,384-column adaptation. Polynomial counting assumes intended real ring laws and is untrusted. Source execution, trace classification and output equivalence still require Lean proofs. These controls are not direct Lean rejections or original-paper mutants.",
        },
    )
    write(
        out / "manifest.json",
        {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()},
    )
    print(
        json.dumps(
            {
                "status": "untrusted-preflight-passed",
                **baseline,
                "controls": len(controls),
                "certificates": 0,
                "full_kernel_proof": False,
            }
        )
    )


if __name__ == "__main__":
    main()
