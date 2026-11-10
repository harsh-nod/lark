# Full-length normalization results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method and commands](README.md), [raw evidence](results/), [paper coverage](../COVERAGE.md).

- **6/6 full-length certificates verified and independently rechecked**: HIP and
  CUDA FP16 RMSNorm, LayerNorm and stable Softmax, each at length 16,384.
- **9/9 scaling certificates verified and independently rechecked**, through
  N=2^31-1 for every family. Larger cases are symbolic proofs; no arrays allocated.
- **3/3 changed programs unproved by Lean**, with zero accepted mutants/timeouts.
  Square arithmetic, variance centering and maximum initialization changes bypass
  the structural screen and fail fixed-program equality (`segmentation_data`).
  These are source-binding checks, not original mutants or semantic diagnosis.
- The reduction-loop and grid proofs conclude the unchanged machine's `Correct`:
  completion, race freedom and every output, for all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 30 | 491,520 | passed |
| mi350-2 | AMD Instinct MI350X | 30 | 491,520 | passed |

Each host compiled the same certificate-bound HIP bytes. Six normal-random trials
and zero, constant, alternating-sign and uniform probes compare every output with
CPU PyTorch, rtol=atol=0.01. Input bytes and 128-byte guards around both allocations
were unchanged. Full binary probes and individual extents are SHA-256-bound.
CUDA profiles were checked by CPU Lean without NVIDIA execution.

## Reduction/grid scaling

One fresh verification plus independent recheck per row. Verify timings include
fresh Python/Lean elaboration while other CPU checks ran concurrently.

| Kind | Vector length | Outcome | Verify seconds | Standalone Lean bytes |
| --- | ---: | --- | ---: | ---: |
| rms | 1 | verified | 18.182 | 111,088 |
| rms | 1,048,576 | verified | 19.848 | 111,148 |
| rms | 2,147,483,647 | verified | 17.767 | 111,178 |
| layer | 1 | verified | 18.055 | 111,186 |
| layer | 1,048,576 | verified | 18.011 | 111,246 |
| layer | 2,147,483,647 | verified | 17.721 | 111,276 |
| softmax | 1 | verified | 17.119 | 111,107 |
| softmax | 1,048,576 | verified | 18.786 | 111,155 |
| softmax | 2,147,483,647 | verified | 17.381 | 111,179 |

One scalar thread/block recomputes reductions for each output, an O(N²) adaptation
with FP32 arithmetic and FP16 storage. RMSNorm/LayerNorm use eps=1e-5, no affine
parameters and population variance. Softmax subtracts the maximum before exp/sum.
The source, launch and harness differ from the authors' optimized implementations;
this study makes no optimized speedup or original model pass-rate/cost claim.

Arithmetic and half conversions are abstract in the theorem. Numerical checks
are separate. Source lowering, closed reference formalization, host contracts,
hardware correspondence and race-free-phase/GPU-interleaving correspondence
remain trusted. The coverage ledger records remaining paper results.
