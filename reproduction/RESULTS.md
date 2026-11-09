# Recorded reproduction results

Run date: 2026-11-09. [Methodology and commands](README.md). [Raw results and proof artifacts](results/).

**Partial independent reproduction; no NVIDIA GPU or model calls were used.** CPU Lean certificates concern reduced float32 programs. The large FP16 HIP programs are independent numerical/performance experiments and are not certified.

| Experiment | Observed | Coverage boundary |
| --- | --- | --- |
| Reduced certificates | 18/18 verified and rechecked | Seven L1 families × two languages, plus sum proxy and minimal repair × two languages |
| Mutations sent directly to Lean | 28/28 unproved, 0 accepted, 0 timeouts | 18 ReLU/GEMM mutants; 10 sum-proxy mutants |
| Equivalent positive controls | 6/6 accepted | Index-plus-zero rewrites |
| Large HIP programs | 17/17 passed; 170 numerical comparisons | All Table 9 workload dimensions; independently declared contracts |
| Exact certified HIP source | 90/90 exact GPU comparisons | Nine reduced sources, with source/reference/task/proof hashes |
| Scalar operations | 1024 comparisons; 0 mismatches | Four operations, finite dyadic strata; Float64-to-FP32 comparison |
| Reported production address conflict | proved | Threads 0/80, output cell 50256; pinned upstream access formula |
| Reference AST versus CPU PyTorch | 336 comparisons passed | Examples, reduced fixtures, larger spatial/group/batch/broadcast cases |

The original paper's 42-mutant set is unavailable. Our rejection counts do not reproduce its 42/42 result. A failed proof attempt does not establish a universal rejection guarantee. The sum proxy is not Softmax.

## Reduced proof coverage

| Family | Input shapes | Output shape | CUDA / HIP |
| --- | --- | --- | --- |
| relu | [4] | [4] | verified / verified |
| gemv | [2, 3], [3, 1] | [2, 1] | verified / verified |
| gemm | [1, 2], [2, 2] | [1, 2] | verified / verified |
| batchmatmul | [2, 1, 2], [2, 2, 2] | [2, 1, 2] | verified / verified |
| linear | [1, 2], [2, 2], [2] | [1, 2] | verified / verified |
| conv2d | [1, 2, 2, 2], [2, 2, 2, 2] | [1, 2, 1, 1] | verified / verified |
| depthwise_conv | [1, 2, 2, 2], [2, 1, 2, 2] | [1, 2, 1, 1] | verified / verified |

SiLU, GELU, Softmax, LayerNorm and RMSNorm remain unsupported formally. There are no original-size FP16 or Level-2 certificates. CUDA profiles were checked on CPU and were not executed on NVIDIA hardware.

## MI300X numerical checks and latency

Device: AMD Instinct MI300X (gfx942); PyTorch 2.14.1+rocm7.2; HIP runtime 7.2.53211. Each numerical case uses six random trials and four probes, rtol=atol=0.01. Each latency is the median of seven rounds of a graph containing 20 calls, in microseconds; compilation is excluded.

| Workload | Our HIP µs | Same-contract eager µs | Same-contract compiled µs | Max absolute error |
| --- | ---: | ---: | ---: | ---: |
| relu | 2.320 | 7.794 | 2.550 | 0 |
| silu | 2.325 | 6.978 | 2.364 | 0 |
| gelu | 2.327 | 7.185 | 2.486 | 0 |
| softmax | 37.021 | 12.541 | 11.679 | 5.96046e-08 |
| layernorm | 32.296 | 15.249 | 7.327 | 0.000488281 |
| rmsnorm | 24.979 | 18.698 | 3.892 | 0 |
| gemv | 254.445 | 13.382 | 2.474 | 0.00195312 |
| gemm | 34.542 | 11.421 | 12.997 | 0.00195312 |
| batchmatmul | 140.162 | 31.022 | 29.276 | 0.00390625 |
| linear | 34.692 | 15.471 | 14.107 | 0.00195312 |
| conv2d | 28.805 | 21.753 | 12.567 | 0.000976562 |
| depthwise_conv | 4.176 | 12.809 | 16.729 | 0.000244141 |
| rope | 2.273 | 23.329 | 2.978 | 0 |
| ffn | 170.267 | 30.722 | 21.993 | 0.0078125 |
| swiglu | 193.652 | 39.006 | 36.443 | 0.015625 |
| flash_attn | 67.229 | 21.570 | 17.520 | 3.05176e-05 |
| gqa | 39.235 | 28.158 | 21.160 | 3.05176e-05 |

Our simple HIP programs are slower than compiled PyTorch in 12/17 workloads. These measurements do not reproduce the paper's optimized kernels or claimed speedups. The references include FP16/FP32 conversion and are not a sweep of the fastest vendor implementations. All seven timing samples are retained in JSON.

The five Level-2 AMD cases are extensions: the paper measures Level-2 on PTX/H100. Our dense attention workload implements the mathematical operation, not the FlashAttention algorithm. Contract choices and rounding/staging differences are documented in the methodology and JSON.

## Small checker experiments

| GEMM segment representation | Checked runs | Median Lean wall seconds |
| --- | ---: | ---: |
| grouped | 2/2 | 7.818 |
| flat | 2/2 | 7.889 |

| Product inner dimension | Lean result | Wall seconds |
| ---: | --- | ---: |
| 1 | proved | 5.131 |
| 2 | proved | 5.702 |
| 4 | proved | 7.284 |
| 8 | proved | 12.097 |

These are small deterministic kernel-checker measurements, with other validation running concurrently. Grouping is a syntax change and does not reproduce the paper's induction/LLM ablation or its scalability claims.

## Production race and trust boundary

The checked witness uses C=50257, block size 1024, unroll factor 8. Thread 0's final-iteration slot 2 reads the clamped address min(50256,51200). Thread 80's slot 1 writes 50256. Both lie in the same block phase and different warps. Lean checks the actual `Lark.conflict` predicate for this pair and checks that the bounds guard excludes the reader. Both witness theorems use no axioms. [Proof source and log](results/production-race/).

The upstream revision is pinned separately from the unavailable paper registry revision. Mapping source to this formula is trusted. This is not a full production-softmax correctness certificate. A tiny identity-valued reproducer has a race despite matching its reference for all symbolic inputs; the repaired version receives full reduced certificates and GPU numerical checks.

Finite hardware comparisons do not establish IEEE semantics, error bounds or complete machine conformance. Reference/source translation and phase-reduction metatheory retain the trust boundary described in [the trust model](../docs/trust.md).

Still unreproduced: original KernelCraft model pass rates/token costs; original FP16/PTX and production-kernel certificates; H100 timings; fastest-library speedups; model/induction ablations; complete opcode calibration and numerical error analysis. Missing original artifacts and unsupported semantics remain blockers independently of NVIDIA hardware access.
