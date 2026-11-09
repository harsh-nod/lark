#!/usr/bin/env python3
"""Prove the paper's thread-0/thread-80 clamped-load witness without a GPU."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", default="lean")
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    source = ROOT / "upstream/llmc_softmax_kernel7.cu"
    text = source.read_text()
    meta = json.loads((ROOT / "upstream/llmc-provenance.json").read_text())
    if hashlib.sha256(source.read_bytes()).hexdigest() != meta["excerpt_sha256"]:
        raise RuntimeError("pinned upstream excerpt changed")
    required = [
        "const int UNROLL_FACTOR = 8;",
        "for (int i = tid; i < C; i += blockDim.x * UNROLL_FACTOR)",
        "reg_array[u] = y[min(C - 1, i + u*blockDim.x)];",
        "if (i + u*blockDim.x < C)",
        "y[i + u*blockDim.x] = reg_array[u] / sum;",
    ]
    if not all(x in text for x in required):
        raise RuntimeError("upstream access pattern changed")
    model = ROOT.parent / "lean/Lark/Model.lean"
    lean = (
        model.read_text()
        + """
namespace ProductionRace
open Lark
def C : Nat := 50257
def blockSize : Nat := 1024
def unroll : Nat := 8
def base (thread : Nat) : Nat := thread + 6 * blockSize * unroll
def address (thread u : Nat) : Nat := min (C-1) (base thread + u*blockSize)
def reader : Access := ⟨0, ⟨.global,0,0,address 0 2⟩,false,⟨0,4,0⟩⟩
def writer : Access := ⟨80,⟨.global,0,0,base 80+blockSize⟩,true,⟨0,4,0⟩⟩

-- Both threads enter the final loop. Reader's unrolled slot is clamped and
-- later discarded. Writer's slot is in bounds and writes the very same cell.
theorem original_address_witness :
    base 0 < C ∧ base 80 < C ∧
    base 0 + 2*blockSize ≥ C ∧ base 80 + blockSize < C ∧
    address 0 2 = 50256 ∧ base 80 + blockSize = 50256 ∧
    conflict ⟨1,blockSize,32⟩ reader writer = true := by decide

theorem guard_eliminates_clamped_read : ¬ (base 0 + 2*blockSize < C) := by decide
#print axioms original_address_witness
#print axioms guard_eliminates_clamped_read
end ProductionRace
"""
    )
    artifact = args.output / "witness.lean"
    artifact.write_text(lean)
    run = subprocess.run([args.lean, str(artifact)], text=True, capture_output=True, timeout=60)
    (args.output / "lean.log").write_text(run.stdout + run.stderr)
    if run.returncode or "sorry" in run.stdout:
        raise RuntimeError(run.stdout + run.stderr)
    if "does not depend on any axioms" not in run.stdout:
        raise RuntimeError("missing axiom audit")
    report = {
        "status": "proved",
        "original_thread_reader": 0,
        "original_thread_writer": 80,
        "C": 50257,
        "block_size": 1024,
        "unroll": 8,
        "reader_base": 49152,
        "reader_slot": 2,
        "reader_unclamped_index": 51200,
        "conflicting_cell": 50256,
        "writer_base": 49232,
        "writer_slot": 1,
        "provenance": meta,
        "model_sha256": hashlib.sha256(model.read_bytes()).hexdigest(),
        "lean_sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
        "axioms": run.stdout,
        "scope": "Arithmetic/access-pair counterexample for pinned upstream final-pass formula, not a full-kernel equivalence proof. Source-to-formula mapping is inspected and trusted.",
    }
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
