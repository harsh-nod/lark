# Elaborated production-reference numerical study

**The original paper is not fully reproduced.** This independent CPU study
implements the numerical specification-validation method described in the
paper's kernel-independent trusted-base appendix. It adds no source certificate,
GPU trial, model call, IEEE theorem or floating-point error bound.

The metaprogram evaluated the actual imported and elaborated Lean references.
The unchanged owned Torch reference files supplied the expected values. All
240 sampled comparisons passed with absolute and relative tolerance `1e-10`
each. The maximum observed absolute difference was
`1.887379141862766e-15`.

| Mathematical reference family | Variants | Sampled comparisons |
| --- | ---: | ---: |
| vLLM SiLU and multiply | 1 | 20 |
| vLLM weighted RMSNorm | 1 | 20 |
| Fused add and RMSNorm | 1 | 20 |
| Native online attention | 1 | 20 |
| vLLM RoPE | 2 layouts | 40 |
| Fused Q/K RMSNorm and RoPE | 2 layouts | 40 |
| FlashInfer RMSNorm | 1 | 20 |
| Guarded SGLang RMSNorm | 1 | 20 |
| Native AWQ GEMM | 1 | 20 |
| llm.c softmax mathematical reference | 1 | 20 |
| **Total** | **12** | **240** |

Each variant uses its existing production-case shape, four input strata and
five output positions. The strata are dyadic, seeded normal, sparse basis with
signed zero, and alternating values with small perturbations. Inputs are
quantized to the declared storage dtype before either reference track runs.
This samples values; it does not enumerate every output or input.

The comparison track uses float64 and explicitly interprets floating storage
casts as identities, matching the exact-real Lean interpretation. Actual-dtype
Torch outputs are also recorded separately. Their maximum sampled absolute
difference from Lean float64 was `0.003606151092210297`; no equality or error
bound for those rounded values is asserted. The original softmax source remains
rejected for its race; evaluating its mathematical reference changes no kernel
acceptance result.

The measured evaluator and driver were frozen at source checkpoint `c9eef4e`.
The evaluator source SHA256 is
`f2e224e2d41ff7602ef78800be83ca66795254cdb2d399c43aaf2a0cf448fe22`.
Lean 4.19.0 and CPU PyTorch `2.11.0+cu130` were used; GPU visibility was disabled
and every tensor operation used CPU. The 48 numerical Lean case processes took
765.83 seconds in total, excluding setup, controls and proof-import builds.

All fourteen numerical negative controls passed, including a doubled expression,
wrong element type, unsupported operation, invalid indices, non-finite values,
and custom addition, numeral and append instances. The
[packet controls](results/production-real-packet-controls-v1/results.json)
also rejected 26 altered scope/data cases after bypassing outer archive hashes.
They synchronize modified log hashes and per-case metadata where needed, and
restore the original evidence before rechecking the positive control.

The [packet](results/production-real-v1/manifest.json) freezes 712 source files
and 240 evidence files inside two archives. It retains all sampled bit patterns,
actual elaborated expressions, unfolded-definition names, inputs, generated
Mains, logs and source bindings. The separate
[verification receipt](results/production-real-packet-verification-v1/results.json)
audits those bytes and records without rerunning Lean. A fresh numerical
recomputation is running and has not yet been counted as complete.

The original authors' registry, formalizations and validation inputs remain
unavailable. These results validate the independent production references in
this repository; they do not reproduce the authors' original validation dataset,
model pass rates, token costs or NVIDIA measurements. Numerical evaluation of all
seventeen independent benchmark reference families remains further work; the
pointwise and GEMV pilots are development evidence and are excluded from the
240 comparisons above.
