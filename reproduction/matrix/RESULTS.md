# Full-size matrix results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **4/4 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 GEMM `[64,256] @ [256,512]` and batched GEMM
  `[32,64,256] @ [32,256,512]`.
- **5/5 scaling certificates verified and independently rechecked**, including
  reduction length 1,048,576 and a BMM output footprint of 1,073,741,824 cells.
  Those larger cases are symbolic proofs; no arrays were allocated or executed.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Arithmetic, batch-address and loop-bound changes bypass the structural frontend
  guard and fail fixed-program equality (`segmentation_data`). This checks source
  binding; it is not the original mutant set or semantic diagnosis/channel census.
- The generic counted-loop/grid proof concludes the existing machine's `Correct`,
  including completion, race freedom, every output, all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 20 | 10,813,440 | passed |
| mi350-2 | AMD Instinct MI350X | 20 | 10,813,440 | passed |

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check all outputs
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. Binary probe bytes and extents are bound
by SHA-256. These are finite numerical checks, with no performance claim. CUDA
profiles were checked by Lean on the CPU, without NVIDIA execution.

## Counted-loop/grid scaling

One fresh verification and independent recheck per row. Verification times include
Python/fresh Lean elaboration while other CPU validation ran concurrently.

| Batch B | Rows M | Reduction K | Columns N | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 1 | 1 | 1 | 1 | verified | 14.973 | 108794 |
| 1 | 64 | 256 | 512 | verified | 13.035 | 108809 |
| 1 | 64 | 1048576 | 512 | verified | 13.075 | 108821 |
| 32 | 64 | 256 | 512 | verified | 13.501 | 108985 |
| 256 | 4096 | 16 | 1024 | verified | 12.834 | 108994 |

The scalar launch uses one thread/block per output and a serial FP32 accumulator,
with FP16 inputs/output. It differs from the authors' optimized kernel, launch
and harness. This study does not reproduce original model pass rates/token
costs, optimized speedups or H100 measurements.

The formal theorem uses abstract arithmetic and half conversions; numerical
checks remain separate. Source lowering, closed reference formalization, host
contracts and the external correspondence between race-free phases and GPU
interleavings remain trusted. The coverage ledger records the remaining results.
