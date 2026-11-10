# Full-size SwiGLU with FP32 projections

This independent adaptation certifies the paper-size contract
`SiLU(X @ Wgate) * (X @ Wup)`, rounded to FP16, then multiplied by `Wdown` with
FP16 output. Shapes are `X=[64,256]`, both up weights `[256,1024]`, and down
weights `[1024,256]`. [Results](RESULTS.md), [evidence](results/),
[paper coverage](../COVERAGE.md).

Four scalar launches compute the gate projection, up projection, SiLU/product,
and down projection. Both projections remain FP32 until the product is stored
as FP16. This preserves the reference's rounding boundary. It is a four-launch
adaptation, distinct from the paper's optimized two-launch implementation and
original PTX proof. Each launch uses one scalar thread/block per output.

[DotMap](../../lean/Lark/DotMap.lean) proves both projection loops and the down
product in the unchanged scalar machine. [SwiPointwise](../../lean/Lark/SwiPointwise.lean)
proves the FP32 SiLU/product lane; [PairMap](../../lean/Lark/PairMap.lean) proves
its full grid and access ownership. [SwiGLU](../../lean/Lark/SwiGLU.lean) connects
all four actual launches through their final memories. Every valid intermediate
read is proved to use the appropriate earlier final memory. The exported theorem
names all four source-derived programs and proves completion, race freedom and
every output, for all inputs and arbitrary outside memories. The standard
precondition is satisfiable. Only `propext`, `Classical.choice` and `Quot.sound`
occur in final axioms.

SiLU uses the tensor reader's exact abstract-operation order,
`gate * (1 / (1 + exp(0 - gate)))`. It is not replaced by an algebraically
equivalent division under arbitrary operation meanings. Small-case tests connect
all four IR interpreters and compare their expressions with the independent
tensor evaluator, covering this order, FP32 identity stores and FP16 rounding.

`verify-swiglu` accepts the four fixed programs, exact typed stage signatures,
eight distinct named allocations, checked shared-input/intermediate wiring,
positive rank-two shapes with footprints below 2^31, native warp widths, and
exact scalar launch/fuel schedules. The complete reference return AST must match
the closed SiLU/two-projection/FP16/down expression before a minimal instance
checks module safety, binding and dtypes. Shape-dependent code cannot lift.

Use Lean 4.19.0 and Python 3.11 or newer at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels verify-swiglu reproduction/swiglu/cases/hip \
  --output /tmp/lark-swiglu --lean "$LARK_LEAN"
python3 -m lark_kernels check /tmp/lark-swiglu --lean "$LARK_LEAN"
python3 reproduction/swiglu/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-swiglu-cpu
python3 reproduction/swiglu/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-swiglu-cpu --output /tmp/lark-swiglu-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/swiglu/run_gpu.py \
  --input /tmp/lark-swiglu-input --output /tmp/lark-swiglu-device
python3 reproduction/swiglu/summarize.py
```

GPU preparation uses CPU PyTorch/NumPy; the device runner uses standard-library
Python and HIP. It reconstructs the wrapper, verifies source/task/reference and
probe hashes, then launches all four stages in order with fixed pointer wiring.
Ten trials check both FP32 projections at rtol=2e-5, atol=2e-6, and every FP16
intermediate/final value at rtol=atol=0.01. Four inputs remain unchanged; all eight
allocations retain 128-byte prefix/suffix guards. Full mixed-precision binary
probe files and individual extents are SHA-256-bound. HIP runs on both MI350X
hosts; CUDA is checked by CPU Lean without NVIDIA execution.

Source lowering, reference formalization, host layouts/disjoint allocations,
ordered launches/pointer wiring, hardware correspondence and the external link
from race-free phases to GPU interleavings remain trusted. The host HIP runtime
is outside the theorem. Arithmetic/half conversions are abstract; numerical
checks are separate. This study uses zero model calls and makes no original
optimized-performance, model pass-rate, token-cost or H100 reproduction claim.
