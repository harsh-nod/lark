# Full-size GEMV results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **2/2 full-size certificates verified and independently rechecked**: HIP and
  CUDA FP16 matrix-vector multiplication, `[512,1024] @ [1024,1] -> [512,1]`.
- **4/4 reduction-scaling certificates verified and independently rechecked**,
  including reduction length 1,048,576. Large proof-only arrays were not allocated.
- **3/3 changed programs unproved by Lean**, zero accepted mutants or timeouts.
  The structural frontend guard was bypassed: arithmetic, address and loop-bound
  changes fail equality with the fixed proved program (`segmentation_data`).
  This is a source-binding check, not the paper's semantic-falsity/diagnosis study.
- The generic counted-loop/grid proof concludes the existing machine's `Correct`:
  completion, race freedom, every output, all inputs and arbitrary outside memory.

## Exact-source MI350X checks

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 10 | 5,120 | passed |
| mi350-2 | AMD Instinct MI350X | 10 | 5,120 | passed |

Each host compiled the same certificate-bound HIP bytes. Six normal-random
trials and zero, constant, alternating-sign and uniform probes check every output
against CPU PyTorch with rtol=atol=0.01. Inputs and 128-byte guards before/after
all three allocations were unchanged. These probes are not exhaustive numerical
conformance or performance measurements. CUDA was checked by Lean on the CPU.

## Counted-loop scaling

One fresh proof and independent recheck per row; proof times include Python and
Lean elaboration while other CPU validation ran concurrently.

| Rows M | Reduction K | Outcome | Verify seconds | Standalone Lean bytes |
| ---: | ---: | --- | ---: | ---: |
| 1 | 1 | verified | 8.538 | 67123 |
| 512 | 16 | verified | 8.719 | 67151 |
| 512 | 1024 | verified | 9.252 | 67171 |
| 512 | 1048576 | verified | 8.735 | 67201 |

The last row describes 536,870,912 matrix cells symbolically. Only the 512×1024
case ran on hardware. The program uses one scalar thread per row and a serial
FP32 accumulator, with FP16 inputs/output. It differs from the authors' optimized
kernel, launch and proof harness. No original model pass rate, token cost,
optimized speedup or H100 result is reproduced by this study.

Arithmetic is abstract in the formal theorem; floating-point calibration and
numerical comparisons remain separate. Source lowering, the closed Torch AST
formalizer, the host interface and race-free-phase hardware correspondence are
trusted. See the coverage ledger for all remaining paper results.
