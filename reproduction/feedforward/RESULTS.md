# Full-size two-launch FFN results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls in this study.**
[Method and commands](README.md), [evidence](results/), [paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP/CUDA
  `[64,256] @ [256,1024]`, ReLU, FP16 intermediate, then `@ [1024,256]` and FP16 output.
- **3/3 scaling certificates verified and independently rechecked**, including
  a million-term first product and a million-cell intermediate/final footprint.
  Larger cases are symbolic proofs without allocating or executing those arrays.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Missing ReLU, changed accumulation and changed second-stage addressing fail
  fixed-program equality after bypassing the structural screen. These check
  source binding, not the original mutation set or semantic diagnosis.
- The final theorem proves completion and race freedom of both actual-machine
  launches, every valid intermediate read from the first final memory, and every
  final output, for all inputs and arbitrary outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Intermediate comparisons | Final comparisons | Inputs / guards |
| --- | --- | ---: | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 10 | 655,360 | 163,840 | passed |
| mi350-2 | AMD Instinct MI350X | 10 | 655,360 | 163,840 | passed |

Both hosts compiled the same two certificate-bound HIP sources. Ten trials check
all intermediate and final outputs against CPU PyTorch, rtol=atol=0.01. Three
input allocations were unchanged and all five allocations retained their
128-byte prefix/suffix guards. Binary probe extents and full files are SHA-256-bound.
CUDA profiles were checked by CPU Lean without NVIDIA execution.

## Pipeline scaling

One fresh verification plus independent recheck per row. Verify timings include
fresh Python/Lean elaboration while other CPU checks ran concurrently.

| Rows M | Input K | Hidden H | Output N | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 1 | 1 | 1 | 1 | verified | 19.655 | 147,733 |
| 64 | 1048576 | 16 | 256 | verified | 20.909 | 147,766 |
| 1024 | 256 | 1024 | 1024 | verified | 17.732 | 147,772 |

Each kernel uses one scalar thread/block per output, serial FP32 accumulation and
FP16 storage. The programs/launches differ from the authors' optimized kernels.
This is a full-size independent FFN adaptation, without an original PTX/H100,
model pass-rate, token-cost or performance reproduction claim.

Arithmetic and half conversions are abstract; numerical checks remain separate.
Source/reference formalization, host layouts, ordered launches and pointer
wiring, hardware correspondence and the external race-free-phase/GPU-interleaving
connection remain trusted. The host HIP runtime is outside the formal theorem.
