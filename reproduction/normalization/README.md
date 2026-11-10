# Full-length normalization induction

This independent extension certifies RMSNorm, LayerNorm and stable Softmax for
FP16 vectors of length 16,384, with FP32 arithmetic and FP16 outputs. HIP and CUDA
have separate source-bound certificates. [Results](RESULTS.md),
[evidence](results/), [paper coverage](../COVERAGE.md).

One scalar thread/block computes each output and recomputes its reductions. This
is a deliberately simple O(N²) launch, with shared input reads and one owned
output per thread. It differs from the paper's optimized kernels and launches.
RMSNorm and LayerNorm have epsilon 1e-5 and no affine parameters. Softmax first
finds the maximum, subtracts it, then sums exponentials. LayerNorm uses population
variance. The references explicitly promote inputs and round outputs to half.

The [FoldPhase library](../../lean/Lark/FoldPhase.lean) checks every instruction
of a five-instruction reduction cycle, then proves the counted loop by induction.
The [Normalization library](../../lean/Lark/Normalization.lean) composes the
initialization, reduction phases, intervening assignments, final load and store.
The [UnaryMap library](../../lean/Lark/UnaryMap.lean) proves the grid fold and
race freedom from shared-read/owned-write access traces. The conclusion is the
unchanged machine's `Correct`: completion, race freedom and every output, for
all inputs, arbitrary outside memory and arbitrary scalar-operation meanings.
Only `propext`, `Classical.choice` and `Quot.sound` occur in the final axioms.

`verify-normalization` accepts one input and output, equal rank-one FP16 shapes
of positive length below 2^31, one thread/block per output, native warp width and
the exact checked instruction schedule and fuel. RMSNorm's second reduction is
skipped by initializing its counter to N; Softmax initializes its maximum from
x[0] and starts at index 1, without assuming max is idempotent. No algebraic laws
are assumed about the abstract operations.

The complete reference return AST must match one of three closed normalization
expressions before a minimal instance checks module safety, binding and dtype.
Shape-dependent branches and extra operators cannot lift through that check.
Small-case tests also compare the actual IR interpreter with the independent
tensor evaluator, including reduction order and half conversions. Source
lowering, reference formalization, host launch/layout contracts, hardware
correspondence and the external link from race-free phases to GPU interleavings
remain trusted. Floating-point error bounds are outside the formal theorem.

Use Lean 4.19.0 and Python 3.11 or newer from the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels verify-normalization reproduction/normalization/cases/softmax/hip/kernel.hip \
  --reference reproduction/normalization/cases/softmax/hip/reference.py \
  --task reproduction/normalization/cases/softmax/hip/task.json \
  --output /tmp/lark-softmax --lean "$LARK_LEAN"
python3 -m lark_kernels check /tmp/lark-softmax --lean "$LARK_LEAN"
python3 reproduction/normalization/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-normalization-cpu
python3 reproduction/normalization/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-normalization-cpu --output /tmp/lark-normalization-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/normalization/run_gpu.py \
  --input /tmp/lark-normalization-input --output /tmp/lark-normalization-device
python3 reproduction/normalization/summarize.py
```

GPU preparation needs CPU PyTorch and NumPy; the device runner uses standard
library Python, the HIP compiler/runtime, shared wrapper validation and the
binary FP16 loader. Every source/reference/task, wrapper, probe extent and full
binary probe file is bound by SHA-256. The runner reconstructs the exact wrapper
before compiling with floating-point contraction disabled. Ten trials per
family compare every output against CPU PyTorch at rtol=atol=0.01, preserve input
bytes and check 128-byte red zones around both allocations. These are finite
numerical checks, separate from the abstract-operation proof. CUDA certificates
are checked by Lean without NVIDIA execution.

Three changed programs bypass the Python structural screen and go directly to
Lean against the fixed program obligations. They must fail `segmentation_data`.
This checks source binding; it is not a semantic diagnosis study or the paper's
original mutants. Scaling through N=2^31-1 proves symbolic statements without
allocating those arrays. This study uses zero model calls and makes no optimized
performance, original model pass-rate, token-cost or H100 reproduction claim.
