# Full-size compiled FP16 PTX GEMV

The [frozen proof packet](results/full-size-gemv-proof-v1/RESULTS.md) retains four
positive Main checks and four direct Lean negative controls. Source-only and
isolated installed-wheel replay passed without model calls or GPU trials.
The [anonymous publication check](results/full-size-gemv-proof-publication-v1/results.json)
matched all 33 changed files (16,674,158 bytes) to source `acd61f0` with TLS
verification enabled. It also checked all five archives, 358 archive members
and 52 wheel/source bindings. This repeated no proof, model or GPU experiment.
The [actual source CI record](results/full-size-gemv-proof-ci-v1/results.json)
records all twenty jobs passing at source `acd61f0`, including the complete
GEMV export/replay and tampering tests and the unchanged paper-ledger checks.
The later receipt commit changes only this document and recorded receipts;
all SDK, Lean, tests, workflow and frozen-snapshot bytes retain the exact
tested source identities.

This development profile checks the independently implemented scalar GEMV's
actual NVRTC-generated PTX, with the unchanged 512×1024 FP16 matrix, 1024×1 FP16
vector and 512×1 FP16 output. The launch is 512 blocks, one active thread per
block, warp width 32. Its original CUDA contract retains fuel `[4102,1,1,1]`.
This is independent evidence; the authors' original optimized PTX and harness
remain unavailable in the inspected artifacts.

The source is the CPU compilation study's PTX 8.8 / `sm_80` output from
NVRTC 12.9.86, SHA-256
`79afeb989948bd8e36278f7b12836e1920727197d6662ddf8b1a642a53a1354c`.
The lossless reader retains all 119 instructions, physical register types,
negative byte offsets, parameter pointers, predicate state and the backward
branch. Parsing alone accepts no proof. Lean independently checks that the
entire parsed program equals the immutable proved program.

The model executes the twelve-instruction prologue, all 64 iterations of the
sixteen-term unrolled loop, the five loop-control instructions and the six
epilogue/return instructions. Each iteration proves the actual load, cast,
product, accumulator, pointer and counter transitions. Loop induction connects
those steps through the real branch and exact exit; it assumes no loop summary.
The `Steps` relation is a finite chain of successful instruction transitions.
It introduces no new fuel or change to the separate CUDA contract.

The complete statement covers all 512 active lanes, successful `ret`, the
actual recorded memory accesses, race freedom and every extracted output.
The reference is the complete closed Python AST for
`(a.float() @ b.float()).half()`, interpreted as an ordered 1,024-term dot
product with the declared scalar conversions. Extra Python statements, swapped
operands and other tensor ASTs refuse. The reference is parsed as data and is
never executed.

Python parsing/reference formalization, logical pointer provenance, aligned
disjoint non-wrapping allocations and scalar-operation correspondence remain
trusted. This proves the declared abstract scalar interpretation. It establishes
no IEEE bit accuracy, rounding error bound, PyTorch backend equivalence or
NVIDIA hardware conformance. It adds no legacy SDK profile, model success or
original paper result.

Use the separate development checker with the actual compiler-study inputs:

```bash
python3 -m lark_kernels.ptx_dot_certificate verify \
  --source /path/to/gemv/kernel/kernel.ptx \
  --reference /path/to/gemv/original/reference.py \
  --contract /path/to/gemv/original/task.json \
  --output /tmp/lark-gemv-ptx-export --lean /path/to/lean-4.19.0/bin/lean

python3 -m lark_kernels.ptx_dot_certificate replay \
  --recording /tmp/lark-gemv-ptx-export --output /tmp/lark-gemv-ptx-replay \
  --lean /path/to/lean-4.19.0/bin/lean

python3 reproduction/ptx/check_dot_controls.py \
  --recording /tmp/lark-gemv-ptx-export --output /tmp/lark-gemv-ptx-controls \
  --lean /path/to/lean-4.19.0/bin/lean
```

Export and replay require the pinned Linux x86-64 Lean 4.19.0 release binary.
Both compile `Nonlinear`, `Pointwise`, `PtxPointwise` and `PtxDot` from matched
trusted source into one fresh import root before checking the generated Main.
New proofs retain `maxRecDepth=10000`, `maxHeartbeats=2000000`, 180 seconds per
Lean process and a 600-second aggregate source-import limit. Existing libraries
retain their original source limits. Replay validates exact input, source,
translation, reference AST, Main, log, axiom, scope and inventory bindings.
Captured Python, Lean and compiled objects are data; replay executes the current
trusted checker and rebuilds its own imports.

The control driver first performs a fresh positive replay. It then checks four
accepted-grammar mutations directly in Lean: wrong product, wrong loop-counter
stride, premature loop exit and conflicting output address. Each must fail at
the immutable `source_program` equality under the same limits and unchanged
task. These check source binding; they are neither a general kernel-falsity
classifier nor the paper's original 42 mutants. Rechecks of the same source
remain one independent development proof.
