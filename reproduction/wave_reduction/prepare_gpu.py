"""Prepare independent CPU and source-expression FP32 outputs for the exact HIP source."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import collective, wave_sum  # noqa: E402


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cpu, out = args.cpu.resolve(), args.output.resolve()
    for name, h in json.loads((cpu / "manifest.json").read_text()).items():
        if sha(cpu / name) != h:
            raise ValueError("CPU evidence differs")
    study = json.loads((cpu / "results.json").read_text())
    if study["status"] != "passed" or not study["baseline"]["rechecked"]:
        raise ValueError("Verified/rechecked CPU evidence required")
    cert = cpu / "certificate"
    report = json.loads((cert / "report.json").read_text())
    for name, h in report["files"].items():
        if sha(cert / name) != h:
            raise ValueError("Certificate differs")
    if report["status"] != "verified" or report["model_profile"] != wave_sum.PROFILE:
        raise ValueError("Real wave-sum certificate required")
    out.mkdir(parents=True, exist_ok=False)
    for name in ("kernel.hip", "reference.py", "task.json", "Main.lean", "report.json"):
        shutil.copyfile(cert / name, out / name)
    import numpy as np
    import torch

    torch.set_num_threads(1)
    if sys.byteorder != "little":
        raise ValueError("Recorded binary format requires little-endian host")
    task, tr, refs = wave_sum.prepare(
        *((cert / n).read_bytes().decode() for n in ("kernel.hip", "reference.py", "task.json"))
    )
    expressions = collective.Machine(task, tr).run().outputs()
    records, rows = [], []

    def add(kind, values, stress=False):
        rows.append(values.float())
        records.append({"trial": len(records), "kind": kind, "stress": stress})

    for index in range(64):
        values = torch.zeros(64)
        values[index] = 1
        add("onehot-" + str(index), values)
    rng = torch.Generator().manual_seed(261102028)
    for index in range(128):
        add("dyadic-" + str(index), torch.randint(-8, 9, (64,), generator=rng).float() / 16)
    for index in range(64):
        add("normal-" + str(index), torch.randn(64, generator=rng) * 0.125)
    positions = torch.arange(64)
    patterns = [
        torch.zeros(64),
        torch.ones(64),
        -torch.ones(64),
        (positions % 2 * 2 - 1).float(),
        (positions.float() - 31.5) / 32,
        (positions % 7 - 3).float() / 8,
        torch.full((64,), 2**-20),
        torch.full((64,), -(2**-20)),
    ]
    for index, values in enumerate(patterns):
        add("pattern-" + str(index), values)
    for index, places in enumerate(
        (
            (0, 1, 2),
            (0, 32, 1),
            (0, 16, 32),
            (0, 63, 31),
            (1, 2, 3),
            (0, 8, 1),
            (7, 39, 8),
            (15, 31, 47),
        )
    ):
        values = torch.zeros(64)
        values[list(places)] = torch.tensor([2**25, -(2**25), 1], dtype=torch.float32)
        add("cancellation-" + str(index), values, stress=True)
    values = torch.stack(rows).contiguous()
    env = {}
    exec(compile((cert / "reference.py").read_text(), "reference.py", "exec"), env)
    independent = torch.stack([env["reference"](row) for row in values]).contiguous()
    cache = {}

    def evaluate(expr):
        if expr in cache:
            return cache[expr]
        if expr.op == "input" and expr.args[0] == 0:
            result = values[:, expr.args[1]]
        elif expr.op == "lit":
            result = torch.full((len(rows),), expr.args[0] / expr.args[1])
        elif expr.op == "bin" and expr.args[0] == "add":
            result = evaluate(expr.args[1]) + evaluate(expr.args[2])
        else:
            raise ValueError("Unexpected reference/source expression")
        cache[expr] = result
        return result

    ast_reference = torch.stack([evaluate(n) for n in refs], dim=1).contiguous()
    # The AST represents the same exact-real sum. Its serial FP32 evaluation can
    # differ from Torch's parallel FP32 sum, so this is recorded numerically.
    source_tree = torch.stack([evaluate(n) for n in expressions], dim=1).contiguous()
    ordinary = sum(not r["stress"] for r in records)
    for data, name in (
        (values, "input.bin"),
        (independent, "reference.bin"),
        (source_tree, "source-tree.bin"),
        (ast_reference, "reference-ast.bin"),
    ):
        (out / name).write_bytes(data.numpy().astype("<f4", copy=False).tobytes())
    atol = rtol = 1e-5
    difference = (source_tree - independent).abs()
    failures = difference > atol + rtol * independent.abs()
    if failures[:ordinary].any():
        raise ValueError("Ordinary source-tree/reference numerical preparation failed")
    metadata = {
        "schema": 1,
        "torch": torch.__version__,
        "numpy": np.__version__,
        "seed": 261102028,
        "trials": records,
        "ordinary_trials": ordinary,
        "stress_trials": len(rows) - ordinary,
        "elements_per_trial": 64,
        "atol": atol,
        "rtol": rtol,
        "ordinary_source_tree_reference_comparisons": ordinary * 64,
        "ordinary_source_tree_reference_failures": int(failures[:ordinary].sum()),
        "stress_source_tree_reference_differences": int(failures[ordinary:].sum()),
        "reference_ast_torch_bit_differences": int(
            (ast_reference.view(torch.int32) != independent.view(torch.int32)).sum()
        ),
        "source_sha256": sha(cert / "kernel.hip"),
        "reference_sha256": sha(cert / "reference.py"),
        "task_sha256": sha(cert / "task.json"),
        "theorem_sha256": sha(cert / "Main.lean"),
        "report_sha256": sha(cert / "report.json"),
        "model_calls": 0,
        "original_paper_fully_reproduced": False,
        "stress_scope": "Fixed cancellation probes explicitly record FP32 disagreement despite exact-real equality; never included as ordinary numerical passes.",
    }
    (out / "dataset.json").write_text(json.dumps(metadata, indent=2) + "\n")
    driver = """#include <hip/hip_runtime.h>
#include "kernel.hip"
extern "C" int launch_wave(void* input, void* output) {
  hipLaunchKernelGGL(wave_sum, dim3(1), dim3(64), 0, 0, (const float*)input, (float*)output);
  return (int)hipGetLastError();
}
extern "C" int runtime_attribute(int which) {
  hipDeviceProp_t p; if (hipGetDeviceProperties(&p, 0) != hipSuccess) return -1;
  return which == 0 ? p.warpSize : which == 1 ? p.maxThreadsPerBlock : -1;
}
"""
    (out / "driver.hip").write_text(driver)
    manifest = {
        "files": {
            p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*")) if p.is_file()
        },
        "generator_sha256": sha(Path(__file__)),
        "original_paper_fully_reproduced": False,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "prepared",
                "ordinary_trials": ordinary,
                "stress_trials": len(rows) - ordinary,
                "ordinary_comparisons": ordinary * 64,
                "stress_disagreements": metadata["stress_source_tree_reference_differences"],
            }
        )
    )


if __name__ == "__main__":
    main()
