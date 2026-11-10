"""Freeze exact source kernels and bit-copy expectations from independent PyTorch ASTs."""

import argparse
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


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    gen = random.Random(261102028)
    special = [
        0,
        0x80000000,
        0x7F800000,
        0xFF800000,
        0x7FC00001,
        0x7F800001,
        1,
        0x80000001,
        0x007FFFFF,
        0x00800000,
        0x7F7FFFFF,
        0xFF7FFFFF,
    ]
    inputs = [0] * 64 + [0x80000000] * 64 + [special[i % len(special)] for i in range(64)]
    inputs += [gen.getrandbits(32) for _ in range(7 * 64)]
    (out / "input.bin").write_bytes(struct.pack("<640I", *inputs))
    expected, rows = [], []
    for case in sorted((ROOT / "cases").iterdir()):
        shutil.copytree(case, out / "cases" / case.name)
        task = Task.read(case / "task.json")
        spec = read_spec((case / "reference.py").read_text(), task)
        if len(spec) != 64 or any(n.op != "input" or n.args[0] != 0 for n in spec):
            raise ValueError("Expected an independent input-permutation tensor reference")
        indices = [n.args[1] for n in spec]
        if any(not 0 <= i < 64 for i in indices):
            raise ValueError("Reference index outside input")
        for trial in range(10):
            expected.extend(inputs[trial * 64 + i] for i in indices)
        rows.append(
            {
                "case": case.name,
                "source_sha256": sha(case / "kernel.hip"),
                "reference_sha256": sha(case / "reference.py"),
                "input_indices": indices,
            }
        )
    (out / "expected.bin").write_bytes(struct.pack("<3200I", *expected))
    for name in ("driver.hip", "run_gpu.py"):
        shutil.copyfile(ROOT / name, out / name)
    manifest = {
        "schema": 1,
        "seed": 261102028,
        "cases": rows,
        "trials": 50,
        "comparisons": 3200,
        "input_generator_sha256": sha(Path(__file__)),
        "files": {str(f.relative_to(out)): sha(f) for f in sorted(out.rglob("*")) if f.is_file()},
        "scope": "Finite exact-bit hardware checks of the same five source files as the full-wave64 certificates. Includes zero, signed zero, infinities, NaN payloads, subnormals and random uint32 payloads; no arithmetic or numerical-error claim.",
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(
        json.dumps(
            {"trials": 50, "comparisons": 3200, "manifest_sha256": sha(out / "manifest.json")}
        )
    )


if __name__ == "__main__":
    main()
