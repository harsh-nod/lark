# Completed Flash/DeepSeek cohorts; full GLM pending

**This is not a completed three-model comparison.** DeepSeek and Flash have
finished all 17 reduced HIP fixtures. The all-model audit still refuses the
unfinished full GLM cohort. These are independent experiments, not the paper's
original pass rates, harness or token costs.

The [completed two-model audit](progress/completed-deepseek-flash-audit/comparison.json)
reconstructs identical first-request messages for all 17 fixtures and freshly
rechecks DeepSeek's successful exported proof.

| Completed local cohort | First-attempt certificates | First requests | Reported first-attempt tokens | Certificates within its recorded budget |
| --- | ---: | ---: | ---: | ---: |
| DeepSeek-V4.1-Flash-1017 | 0 / 17 | 17 | 267,821 | 1 / 17, up to 3 requests/case |
| GLM-5.3-Flash | 0 / 17 | 17 | 312,772 | 0 / 17, 1 request/case |

DeepSeek's later-retry depthwise-convolution certificate is not a first-attempt
success. All 51 DeepSeek requests used 821,063 tokens and reached Lean 37 times.
Flash's 17 requests reached Lean seven times; ten proposals were refused before
Lean. Different retry budgets remain separate. Usage is complete for these
completed cohorts; hosted API spending is zero.

Full GLM-5.3 produced a first-attempt SiLU proof on the independent reduced HIP
fixture. Its [completed case](glm53-budget4096-remote/case-01/result.json), exact
request/response, proposed tactics and exported certificate are preserved.
The [partial-case audit](progress/glm53-silu-partial-audit.json) records matching
model/export tactics, reconstruction of the complete immutable first request,
fixture-byte checks and another successful local Lean recheck. Its request used
7,868 prompt and 4,264 completion tokens, including 4,096 reported reasoning
tokens. This is one completed case within a running cohort, not a 17-case rate.

Both additional Flash batches are complete:
[first seven](flash17-budget4096-half-a-remote/results.json) and
[second seven](flash17-budget4096-half-b-remote/results.json).
Together with the [earlier three cases](../pilot-glm-flash-budget4096-20261109/),
they cover each fixture exactly once. The older
[second-batch audit](progress/flash17-half-b-audit.json) remains a historical
snapshot; the completed two-model audit covers all 17.

The [new Flash runtime](flash17-runtime/flash17-server.json) uses the same pinned
checkpoint/image, native precision, TP=2 and nominal request settings as its
already archived three-case budget variant. It uses a separate owned container
on GPUs 2/3 and port 19085; the earlier three cases used GPUs 6/7 and port 19081.
Readiness, warmup and exact launcher sources are archived here. The
[lifecycle record](progress/flash17-lifecycle-stopped.json) confirms that this
exact owned Flash container was stopped after both controllers exited, both
cohorts finished and active/waiting request gauges reached zero. Its readiness
record remains historical evidence. A warmup is protocol evidence only.
Full GLM's [runtime evidence](../runtime-glm53-20261109/) is separate; its proof
studies continue.

The executed proof controller is the existing
[budget source snapshot](../pilot-deepseek-budget4096-20261109/budget-controller-source.tar.gz),
extended with the disjoint [additional fixture snapshot](../pilot-deepseek-expanded-20261109/additional-cases-source.tar.gz).
Their hashes are retained in the launch records. No running controller or
fixture was edited. Model calls stayed on loopback with zero hosted API spend.

The [comparison method](../../COMPARISON_METHOD.md) requires all 17 fixtures once
per completed cohort. Full GLM archives will be added without modifying these
raw case bytes. The separate [comments-only replay](../../COMMENT_REPLAY_RESULTS.md)
does not alter any response or comparison count: both transformed DeepSeek
candidates remained unproved in Lean.
