# Full-shape independent coverage

**The original paper is not fully reproduced.** This table counts independent
scalar CUDA/HIP contracts at the paper's workload shapes. It does not count
the authors' original kernels, model pass rates or optimized timings.
[Complete paper ledger](COVERAGE.md), [audited machine-readable totals](full-shape-status.json).

All **34 full-shape certificates** (17 HIP + 17 CUDA) verified and independently
rechecked in Lean 4.19.0. Each family also passed ten exact-source HIP trials on
each MI350X host. Inputs and allocation guards stayed unchanged in every trial.
Theorems concern abstract scalar operations; numerical comparisons are separate.

| Independent family / method | HIP + CUDA certificates | Trials: mi350 / mi350-2 | Final comparisons per host | Intermediate comparisons per host |
| --- | ---: | ---: | ---: | ---: |
| [ReLU](pointwise/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [SiLU](pointwise/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [GELU (tanh)](pointwise/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [GEMV](reduction/RESULTS.md) | 2 | 10 / 10 | 5,120 | 0 |
| [GEMM](matrix/RESULTS.md) | 2 | 10 / 10 | 327,680 | 0 |
| [Batched GEMM](matrix/RESULTS.md) | 2 | 10 / 10 | 10,485,760 | 0 |
| [Linear with bias](linear/RESULTS.md) | 2 | 10 / 10 | 327,680 | 0 |
| [Interleaved RoPE](rotary/RESULTS.md) | 2 | 10 / 10 | 327,680 | 0 |
| [Valid Conv2D](convolution/RESULTS.md) | 2 | 10 / 10 | 2,880 | 0 |
| [Depthwise Conv2D](convolution/RESULTS.md) | 2 | 10 / 10 | 46,080 | 0 |
| [RMSNorm](normalization/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [LayerNorm (no affine)](normalization/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [Softmax](normalization/RESULTS.md) | 2 | 10 / 10 | 163,840 | 0 |
| [Two-launch FFN](feedforward/RESULTS.md) | 2 | 10 / 10 | 163,840 | 655,360 |
| [Four-launch SwiGLU](swiglu/RESULTS.md) | 2 | 10 / 10 | 163,840 | 1,966,080 |
| [Dense SDPA (attention workload)](attention/RESULTS.md) | 2 | 10 / 10 | 327,680 | 327,680 |
| [Three-launch GQA](attention/RESULTS.md) | 2 | 10 / 10 | 655,360 | 2,621,440 |
| **Total** | **34** | **170 / 170** | **13,816,640** | **5,570,560** |

Each host checked **19,387,200 scalar values** across these full-shape
sources. Counts include every FP32 projection/score/probability and FP16 hidden
buffer in the multi-launch adaptations. CUDA certificates have no NVIDIA
execution evidence. The largest symbolic scaling cases are separate from these
allocated/executed workloads.

Dense SDPA covers the attention workload shape; it does not implement the
FlashAttention online algorithm. GELU, normalization conventions, precision
boundaries, scalar kernels and launch layouts are explicit independent contracts,
rather than recovered original reference files. A same-source
[dot-product proof ablation](dot_ablation/RESULTS.md) and separate
[shuffle/MFMA hardware conformance](collective_conformance/RESULTS.md) add evidence
for other result categories without converting it into original-paper results.

`python3 reproduction/full_shape_status.py` validates each study's artifact
manifest, completed CPU/device records, certificate anchors and counts before
regenerating this table/JSON. Per-study summarizers additionally reconstruct the
archived source-bound theorem statements and device wrappers. No model calls
are needed. [Local model experiments](local_models/README.md) have separate,
recorded budgets and must not be pooled with these deterministic proof studies.
