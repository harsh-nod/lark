# Full-size valid convolution results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **4/4 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 Conv2D `[1,32,8,8] * [8,32,3,3] -> [1,8,6,6]` and depthwise
  `[1,32,16,16] * [32,1,5,5] -> [1,32,12,12]`, groups=32.
- **5/5 scaling certificates verified and independently rechecked**, including
  a 536,870,912-cell input footprint. Larger cases are symbolic proofs; no arrays
  were allocated or executed.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Arithmetic, kernel-row and output-channel changes bypass the structural frontend
  guard and fail fixed-program equality (`segmentation_data`). This checks source
  binding; it is not the original mutant set or semantic diagnosis/channel census.
- The generic counted-loop/grid proof concludes the existing machine's `Correct`,
  including completion, race freedom, every output, all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 20 | 48,960 | passed |
| mi350-2 | AMD Instinct MI350X | 20 | 48,960 | passed |

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check all outputs
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. Binary probe bytes and extents are bound
by SHA-256. These are finite numerical checks, with no performance claim. CUDA
profiles were checked by Lean on the CPU, without NVIDIA execution.

## Counted-loop/grid scaling

One fresh verification and independent recheck per row. Verification times include
Python/fresh Lean elaboration while other CPU validation ran concurrently.

| Cin | Cout | Input side H | Kernel side K | Groups | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 2 | 1 | 2 | 1 | 1 | verified | 14.201 | 115819 |
| 32 | 8 | 8 | 3 | 1 | verified | 14.001 | 115825 |
| 32 | 32 | 16 | 5 | 32 | verified | 14.203 | 115818 |
| 32 | 8 | 1024 | 3 | 1 | verified | 14.106 | 115848 |
| 32 | 32 | 4096 | 5 | 32 | verified | 14.342 | 115840 |

The scalar launch uses one thread/block per output and a serial FP32 accumulator,
with FP16 inputs/output. Convolution is square NCHW, batch=1, stride=1, padding=0,
with no bias; group counts are 1 or Cin (depthwise). It differs from the authors' optimized kernel, launch
and harness. This study does not reproduce original model pass rates/token
costs, optimized speedups or H100 measurements.

The formal theorem uses abstract arithmetic and half conversions; numerical
checks remain separate. Source lowering, closed reference formalization, host
contracts and the external correspondence between race-free phases and GPU
interleavings remain trusted. The coverage ledger records the remaining results.
