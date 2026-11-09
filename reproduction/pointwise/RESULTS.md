# Full-length pointwise results

Run date: 2026-11-09. **Independent partial reproduction; zero model calls.**
[Method and commands](README.md), [raw evidence](results/),
[full paper coverage](../COVERAGE.md).

- **6/6 full-length certificates verified and independently rechecked**:
  ReLU/SiLU/tanh-GELU, HIP and CUDA, FP16 buffers of length 16,384.
- **6/6 arithmetic mutants unproved directly by Lean**, zero timeouts or accepted
  mutants. Python expression-equality and numerical screens were bypassed.
- **8/8 inductive scaling certificates verified**, including lengths 1,048,576
  and 2,147,483,647. Large arrays were not allocated or executed.
- Existing machine definitions are unchanged. The generic induction theorem
  concludes the actual `LarkNonlinear.Correct`, including completion, race
  freedom, every output, all inputs and arbitrary outside memory.

## Exact-source MI350X validation

| Host | Device | Trials passed | Output comparisons | Input bytes / guards |
| --- | --- | ---: | ---: | --- |
| mi350 | AMD Instinct MI350X | 30 | 491520 | passed |
| mi350-2 | AMD Instinct MI350X | 30 | 491520 | passed |

Each host used the same certificate-bound source bytes, CPU PyTorch expected
values and wrapper. Six random trials and four probes per family check every
output with rtol=atol=0.01. All 128-byte guards before and after both allocations
were unchanged. CUDA source profiles were not executed on NVIDIA hardware.

## Flat evaluator versus induction

Same source, signature, reference and machine; one independent attempt per row.
Times include fresh Lean elaboration and Python overhead, with concurrent
validation on the CPU. Flat checks have a 30-second cap. A timeout means no
certificate within that cap, not that the kernel is incorrect.

| Method | Elements | Outcome | Verify seconds | Standalone Lean bytes |
| --- | ---: | --- | ---: | ---: |
| induction | 1 | verified | 7.281 | 32712 |
| flat | 1 | verified | 4.751 | 17692 |
| induction | 4 | verified | 6.906 | 32712 |
| flat | 4 | verified | 5.985 | 18232 |
| induction | 16 | verified | 7.603 | 32721 |
| flat | 16 | timeout (30 s) | 30.148 | 20425 |
| induction | 64 | verified | 7.879 | 32721 |
| flat | 64 | timeout (30 s) | 30.136 | 29305 |
| induction | 256 | verified | 6.931 | 32730 |
| induction | 16384 | verified | 7.100 | 32748 |
| induction | 1048576 | verified | 7.008 | 32766 |
| induction | 2147483647 | verified | 7.381 | 32793 |

The one-thread-per-block launch is intentionally simple and differs from the
paper's optimized launch. This is a new proof-scaling experiment, not the
original LLM ablation or a speedup reproduction. Arithmetic and half conversions
are abstract operations, not IEEE proofs or numerical-error bounds. The other
14 full-size families, original PTX/production certificates, original model
outcomes/token costs, and H100 timings remain unreproduced.
