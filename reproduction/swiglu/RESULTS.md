# Full-size four-launch SwiGLU results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method and commands](README.md), [evidence](results/), [paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP/CUDA
  `[64,256] @ [256,1024]` gate/up projections kept in FP32, SiLU/product rounded
  to FP16, then `@ [1024,256]` with FP16 output.
- **3/3 scaling certificates verified and independently rechecked**, including
  million-term projections and million-cell intermediates/final outputs. Larger
  cases are symbolic proofs; those arrays were not allocated or executed.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Early half-rounding, changed SiLU and changed down addressing fail fixed-program
  equality after bypassing the structural screen. These check source binding,
  not the original mutation set or semantic diagnosis.
- The final theorem proves completion and race freedom of all four actual
  launches, every valid intermediate read from earlier final memories, and every
  output for all inputs and arbitrary outside memories.

## Exact-source MI350X checks

| Host | Device | Trials passed | FP32 projection comparisons | FP16 intermediate comparisons | Final comparisons | Inputs / guards |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 10 | 1,310,720 | 655,360 | 163,840 | passed |
| mi350-2 | AMD Instinct MI350X | 10 | 1,310,720 | 655,360 | 163,840 | passed |

Each host compiled the same four certificate-bound HIP sources. Ten trials check
both FP32 projections at rtol=2e-5, atol=2e-6, and every FP16 intermediate/final
value at rtol=atol=0.01 against CPU PyTorch. Four inputs were unchanged and all
eight allocations retained 128-byte prefix/suffix guards. Full binary probe
files and individual extents are SHA-256-bound. CUDA profiles were checked by
CPU Lean without NVIDIA execution.

## Pipeline scaling

One fresh verification plus independent recheck per row. Verify timings include
fresh Python/Lean elaboration while other CPU checks ran concurrently.

| Rows M | Input K | Hidden H | Output N | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 1 | 1 | 1 | 1 | verified | 19.642 | 173,418 |
| 64 | 1048576 | 16 | 256 | verified | 21.095 | 173,485 |
| 1024 | 256 | 1024 | 1024 | verified | 19.189 | 173,506 |

This is a four-launch scalar adaptation with FP32 projections and a single FP16
intermediate boundary. It differs from the paper's optimized two-launch kernel
and original PTX proof. SiLU follows the tensor reader's multiplication-by-
reciprocal order; small tests compare the complete connected IR with that reader.
This study makes no optimized-speedup or original model pass-rate/token-cost claim.

Arithmetic and half conversions are abstract; finite numerical checks are separate.
Source/reference formalization, host layouts, ordered launches/pointer wiring,
hardware correspondence and the external race-free-phase/GPU-interleaving link
remain trusted. The host HIP runtime is outside the formal theorem.
