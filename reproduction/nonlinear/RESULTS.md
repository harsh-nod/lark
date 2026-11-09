# MI350X extension results

Run date: 2026-11-09. [Contracts and reproduction commands](README.md). [Raw artifacts](results/).

**Independent reduced-shape certificates and AMD hardware validation. This is not a full reproduction of the original paper. No model calls were made.**

| CPU experiment | Observed | Scope |
| --- | --- | --- |
| New certificates | 25/25 verified and independently rechecked | 17 reduced FP16 HIP families, five FP32 HIP nonlinear families, three FP16 CUDA profiles |
| Direct Lean mutation checks | 28/28 unproved, 0 accepted, 0 timeouts | Independent FP16 ReLU/Softmax/GEMM mutants, HIP and CUDA; Python screen bypassed |
| Equivalent controls | 6/6 proved | Index-plus-zero rewrites |
| Reference AST versus CPU PyTorch | 220 comparisons passed | Six random trials plus four probes for each of 22 source/reference pairs |
| Historical compatibility | All 18 old statements regenerate byte-for-byte | Original scalar-v1 model unchanged |

Half conversions and nonlinear functions are abstract operations in the universally quantified Lean model. These certificates establish source/reference equality in that model, not an IEEE implementation or a numerical-error bound. Source/reference lowering, hardware interpretation, host contracts and concurrency reduction remain trusted.

## Reduced FP16 shapes

| Family | Input shapes | Output shape | HIP certificate |
| --- | --- | --- | --- |
| batchmatmul | [2, 1, 2], [2, 2, 2] | [2, 1, 2] | verified |
| conv2d | [1, 2, 2, 2], [2, 2, 2, 2] | [1, 2, 1, 1] | verified |
| depthwise_conv | [1, 2, 2, 2], [2, 1, 2, 2] | [1, 2, 1, 1] | verified |
| ffn | [1, 2], [2, 2], [2, 2] | [1, 2] | verified |
| flash_attn | [2, 4], [2, 4], [2, 4] | [2, 4] | verified |
| gelu | [4] | [4] | verified |
| gemm | [1, 2], [2, 2] | [1, 2] | verified |
| gemv | [2, 3], [3, 1] | [2, 1] | verified |
| gqa | [2, 2, 1], [1, 2, 1], [1, 2, 1] | [2, 2, 1] | verified |
| layernorm | [4] | [4] | verified |
| linear | [1, 2], [2, 2], [2] | [1, 2] | verified |
| relu | [4] | [4] | verified |
| rmsnorm | [4] | [4] | verified |
| rope | [2, 4], [2, 2], [2, 2] | [2, 4] | verified |
| silu | [4] | [4] | verified |
| softmax | [4] | [4] | verified |
| swiglu | [1, 2], [2, 2], [2, 2], [2, 2] | [1, 2] | verified |

Norms have no affine parameters and epsilon 1e-5. GELU uses the tanh approximation. FFN/SwiGLU round their hidden activation to FP16. RoPE uses supplied tables and adjacent pairs. Dense attention uses head dimension four; GQA uses two query heads, one KV head and **head dimension one**. These are intentionally small independent programs. Neither attention fixture implements the FlashAttention algorithm.

## Exact-source hardware validation

| Host | Device | Kernel trials passed | New scalar comparisons | Binary16 conversion comparisons |
| --- | --- | ---: | ---: | ---: |
| mi350 | AMD Instinct MI350X / gfx950 | 220 | 1024 | 134144 |
| mi350-2 | AMD Instinct MI350X / gfx950 | 220 | 1024 | 134144 |

The same prepared CPU PyTorch values, HIP source bytes, model hashes and certificate index are used on both hosts. Every input byte is preserved. FP16 output comparisons use rtol=atol=0.01; FP32 uses rtol=2e-5 and atol=2e-6. These are numerical tests of the reduced certified sources, separate from Lean checking.

| New scalar operation | mi350 mismatches / samples | mi350-2 mismatches / samples |
| --- | ---: | ---: |
| div | 0/256 | 0/256 |
| exp | 0/256 | 0/256 |
| tanh | 0/256 | 0/256 |
| rsqrt | 0/256 | 0/256 |

Scalar samples compare actual Lean Float64 evaluations, rounded to FP32, against HIP with rtol=2e-6 and atol=1e-6. The complete errors and hashes are in JSON. The half-conversion checks use a separate Python IEEE oracle: all 63,488 finite binary16 encodings are decoded and round-tripped, plus 7,168 finite binary32 conversion inputs with ties, adjacent values, signed zero, overflow and underflow. Both hosts have zero conversion mismatches. NaN/infinite input encodings and exhaustive binary32 conversion are outside this study.

## Large workloads on MI350X

These independent FP16 programs use the Table 9 dimensions, six random trials plus four probes per workload, and the previous graph/event timing protocol. They remain **numerically tested, not Lean-certified at these sizes**.

| Workload | HIP µs | Eager reference µs | Compiled reference µs |
| --- | ---: | ---: | ---: |
| relu | 2.526 | 6.444 | 2.658 |
| silu | 2.496 | 6.560 | 2.868 |
| gelu | 2.518 | 6.434 | 2.656 |
| softmax | 41.899 | 12.544 | 9.378 |
| layernorm | 34.375 | 15.384 | 4.652 |
| rmsnorm | 25.073 | 17.708 | 2.564 |
| gemv | 159.060 | 16.500 | 2.620 |
| gemm | 32.815 | 11.294 | 4.620 |
| batchmatmul | 161.222 | 24.815 | 20.511 |
| linear | 32.901 | 15.686 | 4.748 |
| conv2d | 29.481 | 13.448 | 8.940 |
| depthwise_conv | 4.318 | 12.776 | 16.710 |
| rope | 2.518 | 24.799 | 4.302 |
| ffn | 160.854 | 27.325 | 23.785 |
| swiglu | 184.150 | 36.149 | 31.507 |
| flash_attn | 46.993 | 22.239 | 16.214 |
| gqa | 44.973 | 36.283 | 15.430 |

All 17 workloads passed 170 numerical comparisons; all 17 compiled baselines completed. Our simple HIP kernels are slower than compiled PyTorch on 12/17 workloads. Ratios include the declared reference precision conversions and are not a fastest-vendor-library comparison. The raw record retains every seven-round timing sample.

MI350X results extend the study to gfx950; they do not reproduce H100 or MI300X latency cells or the paper's optimized speedups. The five Level-2 AMD workloads are extensions to the paper's PTX-only Level-2 measurements.

## Remaining gaps

Original registry/kernel/proof artifacts; original-size FP16 and production-kernel certificates; PTX and tensor-core collectives; induction-based scalable proofs; model pass rates/token costs and LLM ablations; H100 timing cells; complete per-opcode hardware sweeps. The independent mutation set is not the paper's original 42 mutants. IEEE proofs and formal numerical-error bounds are outside the paper's main theorem as well as this study.

Lean reduction remains costly even for these reduced cases. The attention kernel computes scores once per query row to avoid duplicate symbolic execution; the GQA dimension is minimal. These choices do not establish paper-scale verification performance. All successful baseline certificates were rechecked and their theorem/source/model hashes are preserved.
