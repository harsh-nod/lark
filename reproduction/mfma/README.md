# Native MFMA tile verification

The opt-in `wave-mfma-v14` profile models
`__builtin_amdgcn_mfma_f32_16x16x16f16` with literal modifiers `(0,0,0)`.
One full wave of 64 lanes holds four half components for each A/B operand and
four float components for C/D. All operands are read from the old register
snapshot before destination updates. The instruction preserves memory,
access traces and memory-order epochs.

The layout follows AMD's [matrix-core programming documentation](https://rocm.blogs.amd.com/software-tools-optimization/matrix-cores-cdna/README.html#builtin-amdgcn-mfma-f32-16x16x16f16)
and [CDNA4 ISA reference](https://www.amd.com/content/dam/amd/en/documents/instinct-tech-docs/instruction-set-architectures/amd-instinct-cdna4-instruction-set-architecture.pdf).
The model describes an exact-arithmetic dot product plus C. It does not model
the hardware's internal accumulation/rounding order or IEEE special values.
Source lowering, logical vector/register packing and operation correspondence
remain trusted; finite hardware checks are separate evidence.

`MFMA.lean` reuses the unchanged nonlinear model for scalar execution, memory
and race freedom. `MFMATile.lean` proves the actual load/matrix/store phases,
their hierarchical launch folds, output extraction and race freedom. The final
theorem quantifies over every scalar interpretation, input and outside-memory
state. No assumed loop summary, admitted theorem or GPU test discharges it.

The source reader accepts the two explicit four-component vector aliases in
the fixture, typed component initializers, component reads and the one builtin.
Other vector operations, pointer reinterpret casts, partial waves/masks,
other MFMA shapes/modifiers and combinations with shuffle instructions are
unsupported. Automatic proofs recognize the fixed single-wave tile program;
other accepted programs need explicit proposals and remain unproved unless
Lean checks their actual statement.

The independent PyTorch AST supplies every reference expression. Exports keep
each output in its own definition to avoid excessive elaboration of a single
expanded declaration. All 256 expressions remain present and are connected to
the tile theorem by a Lean equality proof.

```bash
python3 -m lark_kernels verify-mfma reproduction/mfma/cases/gemm16/kernel.hip \
  --reference reproduction/mfma/cases/gemm16/reference.py \
  --task reproduction/mfma/cases/gemm16/task.json \
  --output /tmp/lark-mfma-certificate --lean /path/to/lean
python3 -m lark_kernels check /tmp/lark-mfma-certificate --lean /path/to/lean

python3 reproduction/mfma/run.py --output /tmp/lark-mfma-study --lean /path/to/lean
python3 reproduction/mfma/summarize.py --output /tmp/lark-mfma-summary.json
```

The summary replays frozen sources, reconstructs every proof statement and
mutation, regenerates the full numerical dataset and audits both GPU archives.
It records prior Lean checks; `lark check` performs a fresh one. Hardware
execution uses `prepare_gpu.py` and `run_gpu.py` on an idle gfx950 GPU.

[Measured results](RESULTS.md) cover this complete 16×16 instruction tile,
not the paper's full GEMM workload, original kernels or production results.
