# Paper result coverage

**The paper has not been fully reproduced.** Independent experiments are separate
from the authors' reported results. Kernel studies used zero model calls. Free
local GLM and DeepSeek inference is recorded as separate adapted experiments; no paid
model endpoints are used. Hardware evidence is from AMD GPUs.

The [source-bound result-by-result audit](paper_results/results/RESULTS.md)
enumerates all 17 tables, seven outer figure groups and 16 additional narrative
anchors in the published preprint. It distinguishes measurements from setup and
method descriptions, binds the published evidence files by hash, and lists the
exact missing inputs. These overlapping items do not define a completion percentage.

[Audited full-shape totals](FULL_SHAPE.md): 34 HIP/CUDA certificates, 170 exact-source
trials and 19,387,200 scalar comparisons per MI350X host. Those counts describe
independent adaptations, not completeness of the original paper.

[Offline model experiment preparation](local_models/README.md) now identifies
official open weights for GLM-5.3, GLM-5.3-Flash and DeepSeek-V4.1-Flash-1017.
This makes local adaptations possible; it does not recover the original harness
or hosted-model outcomes. The [expanded DeepSeek cohort](local_models/DEEPSEEK_RESULTS.md) completed all 17
reduced families with one model-generated depthwise-convolution certificate,
independently exported/rechecked. Its 51 requests used 821,063 reported tokens.
This does not reproduce the original model experiment.
The [completed three-model comparison](local_models/results/model-comparison-20261109/README.md)
audits the same 17 first-request messages for every checkpoint. GLM produced
one first-attempt SiLU certificate; Flash and DeepSeek produced zero first-attempt
certificates. GLM used 832,937 tokens across 49 requests, Flash 312,772 across
17, and DeepSeek 821,063 across 51. Retry budgets remain separate; these are
independent reduced-fixture results, not the original paper's rates. A separate
[comments-only replay](local_models/COMMENT_REPLAY_RESULTS.md) produced no new
certificates and did not alter the raw model results.

Paper: [LARK, arXiv:2611.02028v1](https://arxiv.org/abs/2611.02028v1).
Studies: [CPU/MI300X](RESULTS.md), [nonlinear/MI350X](nonlinear/RESULTS.md),
[full-length pointwise induction](pointwise/RESULTS.md),
[full-size GEMV/counting-loop induction](reduction/RESULTS.md),
[full-size GEMM/BMM induction](matrix/RESULTS.md),
[full-size Linear with bias](linear/RESULTS.md),
[full-size interleaved RoPE](rotary/RESULTS.md),
[full-size valid Conv2D/depthwise](convolution/RESULTS.md),
[full-length RMSNorm/LayerNorm/Softmax](normalization/RESULTS.md),
[full-size two-launch FFN](feedforward/RESULTS.md),
[full-size SwiGLU with FP32 projections](swiglu/RESULTS.md),
[full-size dense SDPA/GQA](attention/RESULTS.md),
[same-source dot-product proof ablation](dot_ablation/RESULTS.md),
[MI350X shuffle/MFMA conformance](collective_conformance/RESULTS.md).
The [bounded scalar PTX study](ptx/RESULTS.md) separately adds four independent
tiny float32 certificates, direct Lean negative controls and CPU-only assembly
checks; it provides no NVIDIA execution evidence.
The [full-wave HIP shuffle study](shuffle/RESULTS.md) adds five whole-launch
Lean certificates, four direct Lean negative controls and 3,200 exact output-bit
comparisons per MI350X host. It formally integrates full-wave register transport;
the earlier MFMA probes remain hardware-only evidence. A separate
[native MFMA tile study](mfma/RESULTS.md) now adds one whole-launch certificate,
four direct Lean controls and 16,850,944 exact-source output-bit comparisons
per host for one AMD matrix-instruction shape with default modifiers.
The [small upstream-derived vLLM SiLU-and-mul study](production_activation/RESULTS.md)
adds HIP/CUDA certificates at two tokens and hidden width five, four direct Lean
controls and exact-source comparisons against an extracted upstream scalar path
on both hosts. Its intermediate FP16 rounding is retained. It does not recover
the original production adaptations or their model outcomes.

| Paper result | Available evidence | Remaining work or dependency |
| --- | --- | --- |
| Level-1 pass rates and per-task results (§5.1, A.4.1) | Independent reduced CUDA/HIP certificates; four tiny scalar PTX certificates; full-size independent CUDA/HIP proofs and exact-source MI350X checks for all twelve Level-1 families | Authors' pinned kernels/registry and harness, original model endpoints/runs, optimized PTX and broader instruction support |
| Five Level-2 PTX proofs (Table 3) | Five independent reduced HIP proofs; full-size HIP/CUDA RoPE, two-launch FFN, four-launch SwiGLU and three-launch dense SDPA/GQA certificates, with exact-source HIP checks | Original PTX kernels/GQA project, FlashAttention online algorithm, optimized launches and collectives |
| All 42 original mutants and rejection channels (§5.2, Tables 4/15) | Independent 28-mutant nonlinear CUDA/HIP study, prior scalar/proxy mutants, six full-length arithmetic mutants and four tiny PTX controls checked directly in Lean | Original mutants/harness, original PTX coverage, model-based diagnosis and second opinions. Independent sets are not the original 42 |
| Nine accepted production kernels (§5.3, Table 5) | One independent upstream-derived SiLU-and-mul family: earlier small fixture plus [native multiwave strided-loop proofs](production_silu/RESULTS.md), eight HIP/CUDA certificates/rechecks at three device-test shapes and two symbolic-only extremes, five direct Lean controls, bit-identical extracted-upstream comparisons across 2,966,860 outputs per MI350X host | All original adapted files, revisions, signatures/departures and production proofs. Packed vector fast paths, in-place buffers, general optimized collective kernels and production reductions remain |
| llm.c data race | Lean witness for a pinned public upstream formula matching reported threads/cell; reduced reproducer/repair | Exact paper registry revision and full adapted kernel; source-to-formula mapping remains trusted |
| Failure-analysis ablations and costs (§5.4, A.4.9) | Deterministic diagnostics, failed proof artifacts, and a separate comments-only replay of two refused DeepSeek candidates (both still unproved) | Original models, prompts, budgets and failures; offline/free constraint excludes paid endpoint calls |
| Segmentation/flat ablation (§5.4, A.4.8) | Pointwise and counted-loop GEMV/GEMM/BMM induction concluding existing machine `Correct`; same-source pointwise and GEMV flat/induction timing comparisons (GEMV flat verified through K=16, timed out at K=32/64/128; induction verified/rechecked all eight sizes) | Original kernels, agent prompts and LLM runs; scalable profiles use one-thread blocks |
| Verification scaling (A.4.4) | Independent ReLU proofs through length 2^31-1, GEMV/GEMM reduction through K=1,048,576 BMM output footprints through 2^30, all three normalization families through N=2^31-1, and connected attention through 4,096-token rows / 1,048,576-wide projections | Original kernels, tiled/online attention, original token/time measurements |
| Model size versus pass rates/tokens (A.4.6) | Completed 17-fixture cohorts for GLM, Flash and DeepSeek with identical decoded first requests; first certificates 1 / 0 / 0, separate retry results 1 / 0 / 1, audited table and SVG | Original model versions, harness, token accounting and runs; tokenizers/precision/TP differ, so no isolated model-size conclusion |
| Stage token costs (A.4.3) | Completed matched cohorts: GLM 832,937 tokens / 36 Lean checks, Flash 312,772 / 7, DeepSeek 821,063 / 37; earlier pilots and reasoning-only runs archived separately | Original stage traces/endpoints and stage boundaries; local inference does not reproduce billed costs |
| Refusal census and hard Level-1 tasks (A.4.2/A.4.5) | Strict refusals; full-size independent BatchMatmul/DepthwiseConv certificates and device checks | Original failed runs/statements; smaller proofs do not contradict the paper's model outcomes |
| Race-freedom fallback (A.4.7) | llm.c conflict witness and generic pointwise ownership proof | Original fallback conversations, second opinions and token costs |
| Latencies/speedups (A.4.10, Table 14/Figure 7) | Independent 17-workload FP16 numerical checks and eager/compiled timings on MI300X/MI350X | Authors' optimized kernels/reference contracts, fastest vendor baselines, H100 for original PTX/CUDA cells |
| Per-operation conformance (A.5) | Eight scalar operation samples on AMD; exhaustive finite-half decode/roundtrip, sampled FP32-to-half conversions, full-partition shuffle layouts and one native MFMA shape with exhaustive basis-pair probes on two MI350X hosts; five formal shuffle certificates and one formal native MFMA tile certificate, each with exact-source hardware checks | Full instruction table, combined/tiled collective programs, masked/partial-wave and other vector/alignment/collective forms and modifiers, NVIDIA hardware for NVIDIA operations. Samples are not complete semantics |
| Retargeting effort/source counts (A.6) | Independent CUDA/HIP and bounded scalar PTX readers sharing a machine | Authors' source tree and development history; historical person-days cannot be regenerated by an independent implementation |
| Supplementary GQA project (A.12) | Full-size three-launch GQA certificate, source-bound FP32 intermediates and exact-source checks on both MI350X hosts | Authors' actual supplementary project not found in the manuscript source archive or searched release endpoints |

The [artifact audit](pointwise/results/artifact-audit.json) and
[repeated public checks](results/artifact-reaudit-20261110.json) record specific public
GitHub queries and the empty `AICrossSim/KernelCraft` metadata. The [arXiv source
inventory](results/paper-source-manifest.json) has manuscript files/figures and no
implementation. These bounded searches do not prove that artifacts cannot exist
elsewhere or be released later.
The [expanded author-repository check](results/artifact-expanded-20261110.json)
also records the public `gpu_optim_bench` repository: its inspected revision
identifies itself as FlashInfer-Bench and has no LARK/Lean/KernelCraft-named
path or Lean/PTX/HIP file in its complete tree. This bounded tree/README check
does not exclude relevant material elsewhere.

All 17 workload shapes now have independent full-size contracts and exact-source
HIP checks. Dense SDPA covers the attention workload, not FlashAttention's online
algorithm. Software work remains: optimized/tiled/online kernels, broader PTX and
collective semantics, actual adapted production sources, and corresponding
hardware validation. It cannot recover missing original model outcomes, source
revisions, historical development effort or H100 measurements. AMD adaptations
and independent experiments remain labeled as such.
