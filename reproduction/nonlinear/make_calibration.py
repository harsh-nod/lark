"""Evaluate the new abstract scalar operations using a finite Lean Float interpretation."""

import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import struct
import subprocess

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--lean", default="lean")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    rng = random.Random(261102028)
    x = [0.0, 1.0, -1.0, 10.0, -10.0] + [rng.randint(-320, 320) / 32 for _ in range(251)]
    positive = [2.0**e for e in (-20, -10, 0, 10, 20)] + [
        rng.randint(1, 1024) / 64 for _ in range(251)
    ]
    model = ROOT.parents[1] / "lean/Lark/Nonlinear.lean"

    def literal(v):
        n, d = v.as_integer_ratio()
        return f"(Float.ofInt ({n}) / Float.ofNat {d})"

    pairs = "[" + ", ".join(f"({literal(a)},{literal(b)})" for a, b in zip(x, positive)) + "]"
    source = args.output / "calibration.lean"
    source.write_text(
        model.read_text()
        + f"""
namespace NonlinearCalibration
open LarkNonlinear
set_option maxRecDepth 100000
def ops : Ops Float := ⟨fun n d => Float.ofInt n / Float.ofNat d,
 (· + ·), (· - ·), (· * ·), fun a b => if a < b then b else a,
 (· / ·), Float.exp, Float.tanh, fun a => 1.0 / Float.sqrt a,
 id, id⟩
-- Half conversions are not evaluated in this Float interpretation; the hardware
-- conversion probe uses a separate Python IEEE binary16 oracle.
def pairs : List (Float × Float) := {pairs}
#eval pairs.map (fun (a,b) => (applyBinary ops .div a b).toBits.toNat)
#eval pairs.map (fun (a,_) => (applyUnary ops .exp a).toBits.toNat)
#eval pairs.map (fun (a,_) => (applyUnary ops .tanh a).toBits.toNat)
#eval pairs.map (fun (_,b) => (applyUnary ops .rsqrt b).toBits.toNat)
end NonlinearCalibration
"""
    )
    run = subprocess.run([args.lean, str(source)], capture_output=True, text=True, timeout=120)
    (args.output / "lean.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    bits = [json.loads(s) for s in re.findall(r"\[[0-9,\s]*\]", run.stdout)]
    assert len(bits) == 4 and all(len(row) == 256 for row in bits)
    values = [[struct.unpack("<d", struct.pack("<Q", n))[0] for n in row] for row in bits]
    data = {
        "seed": 261102028,
        "x": x,
        "positive": positive,
        "ops": ["div", "exp", "tanh", "rsqrt"],
        "lean_results": values,
        "lean_bits": bits,
        "model_sha256": sha(model),
        "lean_source_sha256": sha(source),
        "scope": "Finite normal dyadic operands only. GPU FP32 is compared to rounded Lean Float64 with rtol=2e-6 and atol=1e-6. Half casts are abstract and checked separately against Python binary16 conversions.",
    }
    (args.output / "operands.json").write_text(json.dumps(data, indent=2) + "\n")
    print(args.output / "operands.json")


if __name__ == "__main__":
    main()
