# Full-size dense SDPA and GQA results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method](README.md), [evidence](results/), [paper coverage](../COVERAGE.md).

- **4/4 full-size certificates verified and independently rechecked**: HIP/CUDA
  dense attention Q/K/V `[1,128,256]`, and GQA Q `[8,128,64]`, K/V `[2,128,64]`.
- **4/4 scaling certificates verified and independently rechecked**, including
  4,096-token rows and 1,048,576-wide projections. Scaling arrays were not allocated.
- **4/4 changed programs unproved by Lean**, zero accepted/timeouts. Changed KV
  groups, score scale, softmax seed loop and value heads fail fixed-program equality
  after bypassing the structural screen. This checks source binding, not semantic
  diagnosis or the original mutation set.
- The theorem proves completion and race freedom of all three actual launches,
  grouped KV addressing, both FP32 intermediate buffers, every valid intermediate
  read from earlier final memories and every output, for all inputs/outside memories.

## Exact-source MI350X checks

| Host | Family | Trials passed | FP32 intermediate comparisons | FP16 final comparisons | Inputs / guards |
| --- | --- | ---: | ---: | ---: | --- |
| mi350 | dense | 10 | 327,680 | 327,680 | passed |
| mi350 | gqa | 10 | 2,621,440 | 655,360 | passed |
| mi350-2 | dense | 10 | 327,680 | 327,680 | passed |
| mi350-2 | gqa | 10 | 2,621,440 | 655,360 | passed |

Each host passed 20 trials and 3,932,160 scalar comparisons. The three exact
certificate-bound HIP stages use FP16 Q/K/V, FP32 scaled scores and row softmax,
then FP16 output. Every intermediate is checked against CPU PyTorch at rtol=2e-5,
atol=2e-6; final outputs use rtol=atol=0.01. Three inputs stayed byte-identical;
all six allocations retained 128-byte prefix/suffix guards. Probe files/extents
and actual compiled wrappers are SHA-256-bound. CUDA certificates were checked
by CPU Lean without NVIDIA execution.

## Symbolic scaling

Fresh verification plus independent recheck per row. Timings include elaboration
while other checks ran concurrently.

| Query heads | KV heads | Sequence | Dimension | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 1 | 1 | 1 | 1 | verified | 27.963 | 212,232 |
| 4 | 2 | 2 | 4 | verified | 25.490 | 212,235 |
| 1 | 1 | 4096 | 64 | verified | 25.528 | 212,349 |
| 8 | 2 | 128 | 1048576 | verified | 25.471 | 212,381 |

These are three-launch scalar, noncausal dense SDPA/GQA adaptations. The dense
case covers the paper's attention workload shape, not the FlashAttention online
softmax algorithm, optimized original kernel or PTX proof. No optimized-speedup,
H100 timing, original model pass-rate or original token-cost claim is made.
Small tests compare the entire connected IR with the independent tensor reader,
including scale, max initialization, grouping and precision boundaries.

Arithmetic and half conversions are abstract; finite numerical checks are separate.
Source/reference formalization, host layouts, ordered launches/pointer wiring,
hardware correspondence and the external race-free-phase/GPU-interleaving link
remain trusted. The host HIP runtime is outside the theorem.
