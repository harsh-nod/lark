# Full-size RoPE results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 interleaved RoPE at `[256,128]`, with `[256,64]` cosine/sine inputs.
- **4/4 scaling certificates verified and independently rechecked**, including
  a 2,147,483,646-cell output footprint. Larger cases are symbolic proofs; no
  arrays were allocated or executed.
- **3/3 changed programs unproved by Lean**, zero accepted mutants/timeouts.
  Arithmetic, parity and pair-index changes bypass the structural frontend
  guard and fail fixed-program equality (`segmentation_data`). This checks source
  binding; it is not the original mutant set or semantic diagnosis/channel census.
- The branch/grid induction proof concludes the existing machine's `Correct`,
  including completion, race freedom, every output, all inputs and outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 10 | 327,680 | passed |
| mi350-2 | AMD Instinct MI350X | 10 | 327,680 | passed |

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check all outputs
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. Binary probe bytes and extents are bound
by SHA-256. These are finite numerical checks, with no performance claim. CUDA
profiles were checked by Lean on the CPU, without NVIDIA execution.

## Branch/grid scaling

One fresh verification and independent recheck per row. Verification times include
Python/fresh Lean elaboration while other CPU validation ran concurrently.

| Rows M | Width D | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | --- | ---: | ---: |
| 1 | 2 | verified | 19.644 | 165547 |
| 256 | 128 | verified | 20.936 | 165583 |
| 1048576 | 128 | verified | 22.035 | 165612 |
| 1073741823 | 2 | verified | 20.984 | 165628 |

The scalar launch uses one thread/block per output and branches on output parity,
with FP16 inputs/output and FP32 multiplication/addition/subtraction. It differs from the authors' optimized kernel, launch
and harness. This study does not reproduce original model pass rates/token
costs, optimized speedups or H100 measurements.

The formal theorem uses abstract arithmetic and half conversions; numerical
checks remain separate. Source lowering, closed reference formalization, host
contracts and the external correspondence between race-free phases and GPU
interleavings remain trusted. The coverage ledger records the remaining results.
