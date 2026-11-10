# Partial collection while the remaining cohorts run

**This is not a completed three-model comparison.** The all-model audit refuses
this collection until every required run has a real finished `results.json`.
Nothing here supplies the original paper's pass rates or token costs.

Full GLM-5.3 produced a first-attempt SiLU proof on the independent reduced HIP
fixture. Its [completed case](glm53-budget4096-remote/case-01/result.json), exact
request/response, proposed tactics and exported certificate are preserved.
The [partial-case audit](progress/glm53-silu-partial-audit.json) records matching
model/export tactics, reconstruction of the complete immutable first request,
fixture-byte checks and another successful local Lean recheck. Its request used
7,868 prompt and 4,264 completion tokens, including 4,096 reported reasoning
tokens. This is one completed case within a running cohort, not a 17-case rate.

The [completed second Flash batch](flash17-budget4096-half-b-remote/results.json)
contains seven one-request cases: GEMV, GQA, LayerNorm, Linear, RMSNorm, RoPE and
SwiGLU. Four reached Lean and were unproved; three proposals were refused before
Lean. There are no verified certificates in this batch. Its seven responses
report 76,871 prompt and 31,930 completion tokens (108,801 total; 28,672 reasoning).
The [batch audit](progress/flash17-half-b-audit.json) reconstructs every request
and preserves the distinct outcomes. The other seven-case batch is still live.

The [new Flash runtime](flash17-runtime/flash17-server.json) uses the same pinned
checkpoint/image, native precision, TP=2 and nominal request settings as its
already archived three-case budget variant. It uses a separate owned container
on GPUs 2/3 and port 19085; the earlier three cases used GPUs 6/7 and port 19081.
Readiness, warmup and exact launcher sources are archived here. A warmup is
protocol evidence only. Full GLM's [runtime evidence](../runtime-glm53-20261109/)
is recorded separately.

The executed proof controller is the existing
[budget source snapshot](../pilot-deepseek-budget4096-20261109/budget-controller-source.tar.gz),
extended with the disjoint [additional fixture snapshot](../pilot-deepseek-expanded-20261109/additional-cases-source.tar.gz).
Their hashes are retained in the launch records. No running controller or
fixture was edited. Model calls stayed on loopback with zero hosted API spend.

The [comparison method](../../COMPARISON_METHOD.md) keeps first attempts separate
from retries and requires all 17 fixtures exactly once for a completed model
cohort. Completed archives will be added without modifying these raw case bytes.
