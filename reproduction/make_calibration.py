#!/usr/bin/env python3
"""Evaluate the actual Lean scalar-op definitions on pinned finite operands."""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import re
import struct
import subprocess


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", default="lean")
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    model = Path(__file__).resolve().parent.parent / "lean/Lark/Model.lean"
    rng = random.Random(261102028)
    boundaries = [0.0, 1.0, -1.0] + [
        sign * 2.0**e for e in (-20, -10, 0, 10, 20) for sign in (-1, 1)
    ]
    a = boundaries + [rng.randint(-65536, 65536) / 256 for _ in range(256 - len(boundaries))]
    b = list(reversed(boundaries)) + [
        rng.randint(-65536, 65536) / 256 for _ in range(256 - len(boundaries))
    ]

    def lit(v):
        f = Fraction(v)
        return f"(Float.ofInt ({f.numerator}) / Float.ofNat {f.denominator})"

    pairs = "[" + ", ".join(f"({lit(x)}, {lit(y)})" for x, y in zip(a, b)) + "]"
    source = args.output / "calibration.lean"
    source.write_text(
        model.read_text()
        + f"""
namespace Calibration
open Lark
set_option maxRecDepth 100000
def ops : Ops Float := ⟨fun n d => Float.ofInt n / Float.ofNat d,
  (· + ·), (· - ·), (· * ·), fun a b => if a < b then b else a⟩
def pairs : List (Float × Float) := {pairs}
"""
        + "\n".join(
            f"#eval pairs.map (fun (a,b) => (applyBinary ops .{op} a b).toBits.toNat)"
            for op in ("add", "sub", "mul", "max")
        )
        + "\nend Calibration\n"
    )
    run = subprocess.run([args.lean, str(source)], text=True, capture_output=True, timeout=150)
    (args.output / "lean.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    bits = [json.loads(value) for value in re.findall(r"\[[0-9,\s]*\]", run.stdout)]
    if len(bits) != 4 or any(len(row) != 256 for row in bits):
        raise RuntimeError("missing Lean results")
    values = [[struct.unpack("<d", struct.pack("<Q", v))[0] for v in row] for row in bits]
    data = {
        "seed": 261102028,
        "a": a,
        "b": b,
        "lean_results": values,
        "lean_result_bits": bits,
        "model_sha256": digest(model),
        "lean_source_sha256": digest(source),
        "strata": "zero, signs, powers of two 2^-20..2^20, random dyadic finite values; no subnormals/NaNs/infinities",
    }
    (args.output / "operands.json").write_text(json.dumps(data, indent=2) + "\n")
    print(args.output / "operands.json")


if __name__ == "__main__":
    main()
