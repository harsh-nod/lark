# Full-size two-launch FFN

This independent extension certifies the paper-size ReLU feed-forward contract
`[64,256] @ [256,1024]`, ReLU followed by FP16 intermediate storage, then
`[64,1024] @ [1024,256]` with FP16 output. Both products accumulate in FP32.
[Results](RESULTS.md), [evidence](results/), [paper coverage](../COVERAGE.md).

The first scalar kernel writes the complete intermediate; the second reads that
same buffer. Each uses one thread/block per output and a serial dot product.
These are independent programs and launches, with separate HIP/CUDA certificates,
and differ from the paper's optimized kernels and original PTX proof.

[DotMap](../../lean/Lark/DotMap.lean) proves counted dot loops, pure output
expressions and grid folds in the unchanged nonlinear machine. It reuses checked
matrix-address profiles and supports explicit input conversion choices. For FFN,
both inputs are promoted from FP16; the first output expression applies ReLU
before rounding to FP16. The second stage promotes that stored intermediate.
No algebraic laws about arithmetic or half conversion are assumed.

[Pipeline](../../lean/Lark/Pipeline.lean) connects the second launch to the actual
first final memory. Its compatibility proof equates the intermediate allocation
sizes, and every valid second-stage intermediate read is proved to use that
memory. The [FeedForward theorem](../../lean/Lark/FeedForward.lean) instantiates
both stages. The final exported statement names both source-derived programs
and proves completion, race freedom, intermediate dataflow and every final output
for every input and arbitrary outside memory. A second theorem accepts a
satisfiable standard precondition. Final axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

`verify-ffn` requires two positive rank-two FP16 matmul signatures, equal named
intermediate buffers, distinct entries, five disjoint named allocations, the
native warp width, exact scalar launch/fuel and the checked two programs. Every
buffer footprint must be below 2^31. The full reference AST must be exactly
`((x.float() @ w1.float()).relu().half().float() @ down.float()).half()`;
module safety and binding are then checked on a minimal instance. ReLU/rounding
reordering and shape-dependent branches cannot lift through that check. Small
tests independently compare the connected IR expressions with the tensor reader.

Use Lean 4.19.0 and Python 3.11 or newer at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels verify-ffn reproduction/feedforward/cases/hip \
  --output /tmp/lark-ffn --lean "$LARK_LEAN"
python3 -m lark_kernels check /tmp/lark-ffn --lean "$LARK_LEAN"
python3 reproduction/feedforward/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-ffn-cpu
python3 reproduction/feedforward/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-ffn-cpu --output /tmp/lark-ffn-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/feedforward/run_gpu.py \
  --input /tmp/lark-ffn-input --output /tmp/lark-ffn-device
python3 reproduction/feedforward/summarize.py
```

GPU preparation uses CPU PyTorch/NumPy; the device runner uses the Python standard
library and HIP compiler/runtime. It reconstructs the wrapper, checks every
source/task/reference hash, and launches the two kernels in order with the same
intermediate allocation. Ten trials compare every intermediate and final value
against CPU PyTorch, rtol=atol=0.01. Three inputs are preserved byte-for-byte and
all five allocations have 128-byte guards on both sides. Full binary probes and
individual extents are SHA-256-bound. HIP runs on both MI350X hosts; CUDA is checked
by CPU Lean without NVIDIA execution.

Source lowering, closed reference formalization, host layouts/disjoint allocations,
ordered launches and pointer wiring, hardware correspondence and the external
race-free-phase/GPU-interleaving connection remain trusted. The mathematical
pipeline proves dataflow between machine states; it does not verify the host HIP
runtime. Arithmetic/half conversions remain abstract and finite numerical checks
are separate. This study makes no optimized-performance, original model pass-rate,
token-cost or H100 claim and uses zero model calls.
