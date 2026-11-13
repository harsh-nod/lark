# Complete compiled FP16 PTX GEMM development profile

This separate checker proves the exact independently compiled 64×256 by
256×512 matrix multiplication. It preserves the original FP16 buffers,
grid 32768, block one, warp 32 and CUDA contract fuel `[1030,1,1,1]`.
The compiler study's complete 171-instruction PTX source is retained in
[the pinned case](full-size/gemm/README.md).

The lossless reader translates all instructions, including the five additional
integer operations used for row/column addressing. The immutable Main binds the
entire parsed program and the closed reference `(a.float() @ b.float()).half()`.
Lean checks the 47-instruction prologue, all sixteen iterations of the actual
backward loop, its pointer/counter/predicate control, the output store and ret.
The theorem covers all 32,768 active lanes, race freedom of the actual memory
trace, every extracted output against an ordered 256-term reference, and memory
preservation outside the output footprint. PTX execution uses finite successful
instruction transitions; CUDA fuel remains data for its separate semantics.

```bash
python3 -m lark_kernels.ptx_matrix_certificate verify \
  --source reproduction/ptx/full-size/gemm/kernel.ptx \
  --reference reproduction/ptx/full-size/gemm/reference.py \
  --contract reproduction/ptx/full-size/gemm/task.json \
  --output /tmp/lark-ptx-gemm-export --lean /absolute/path/to/lean

python3 -m lark_kernels.ptx_matrix_certificate replay \
  --recording /tmp/lark-ptx-gemm-export \
  --output /tmp/lark-ptx-gemm-replay --lean /absolute/path/to/lean

python3 reproduction/ptx/check_matrix_controls.py \
  --recording /tmp/lark-ptx-gemm-export \
  --output /tmp/lark-ptx-gemm-controls --lean /absolute/path/to/lean
```

[The retained results](results/full-size-gemm-proof-v1/RESULTS.md) include four
successful Main checks, 20 fresh owned-module builds, four direct Lean
source-binding refusals and an offline installed-wheel replay. These repeated
checks cover one independent development kernel.

Lean 4.19.0 is pinned by its binary hash. Export and replay compile all five
owned modules from matched trusted source in a fresh import root and check six
Main obligations. Captured Python, Lean and oleans are hash-bound data. They are
not executed or loaded during replay. Limits remain maxRecDepth 10000,
maxHeartbeats 2000000, 180 seconds per Lean process and 600 seconds per import
aggregate. Legacy libraries retain their own original source limits.

The direct controls change one product, loop-counter stride, B pointer stride
or output address while preserving the task. They test refusal of changed
source by this fixed profile, rather than general classification of incorrect
kernels or the paper's original 42 mutants.

The semantics use declared abstract scalar operations. Python parsing/reference
formalization, scalar-operation correspondence, logical pointer provenance and
aligned disjoint non-wrapping allocations remain trusted. No IEEE rounding/error
bound, PyTorch backend equivalence, NVIDIA execution/conformance, original
optimized kernel or original model result is established. This profile adds no
legacy `lark verify` registration or model-cohort success.

The package version is 0.2.0. The frozen GEMV 0.1.0 recording pins its complete
SDK source roster, so it must be replayed with its recorded 0.1.0 wheel. Adding
the two GEMM SDK modules changes that roster even though the old source files
and generated GEMV Main remain unchanged. The checker deliberately keeps that
strict refusal; a new GEMV recording made with 0.2.0 binds the new roster.
