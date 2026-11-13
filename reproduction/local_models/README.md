# Offline local-model experiments

The [completed full-size DeepSeek HIP cohort](results/full-shape-cohort-deepseek-v1/results.json)
verified sixteen of seventeen fixed-scaffold tasks within the common budget.
Depthwise convolution exhausted its budget. All 175 requests and responses are
retained: 3,361,778 prompt tokens and 482,540 completion tokens, 3,844,318 total.
The first response verified zero proofs; fourteen cases verified at their first
actual Lean check. The latter excludes earlier policy/syntax refusals and source
reads and is not original-paper Pass@1. The complete protocol replay regenerated
all prompts, actions and Main files; accepted proofs passed 32 additional fresh
Lean kernel/axiom checks. Failed candidates retain their recorded outcomes.
These are model proof completions for the owned full-size fixtures, with zero
new registered source certificates or original-paper result claims.

The [completed full-size Flash HIP cohort](results/full-shape-cohort-flash-hip-v1/results.json)
verified twelve of seventeen tasks. ReLU, LayerNorm, Softmax, RoPE and FFN
exhausted their budgets; their attempts and costs remain archived. All 93
requests used 1,563,506 prompt and 115,224 completion tokens, 1,678,730 total.
Zero first responses verified a proof; five tasks verified at their first
actual Lean check, which is a separate metric. Full protocol replay bound every
request, and all twelve accepted proofs passed 24 additional fresh kernel/axiom
checks. Its exact owned, drained two-GPU service was stopped with exit code zero.
GLM HIP and the GLM and DeepSeek CUDA-source cohorts remain unfinished experiments.

The [completed full-size Flash CUDA cohort](results/full-shape-cohort-flash-cuda-v1/results.json)
verified nine of seventeen tasks. ReLU, RMSNorm, Softmax, GEMM, BMM, Conv2D,
depthwise convolution and GQA exhausted their budgets. All 108 requests and
responses remain archived: 1,841,471 prompt and 164,371 completion tokens,
2,005,842 total. Zero first responses verified a proof; three tasks verified at
their first actual Lean check. Complete protocol replay bound every request,
and the nine accepted proofs passed 18 additional fresh kernel/axiom checks.
The exact owned, drained two-GPU service was stopped with exit code zero.
CUDA identifies the proof-task source language; serving used MI350X GPUs and
Lean checks ran on CPU. These are independent fixed-scaffold model outcomes.

The [full-size comparison tool](compare_full_shape.py) reconstructs per-task
costs from the archived responses and applies success-only input/output token
averages separately to twelve Level-1 and five Level-2 tasks. It keeps failed-task
costs in cohort totals and requires an explicit partial-roster flag until all
three models on both source languages are supplied. See the
[protocol and command](FULL_SHAPE_METHOD.md) for its evidence checks and limits.
The [initial partial-roster report](results/full-shape-comparison-deepseek-v1/RESULTS.md)
uses the complete DeepSeek HIP cohort. Its success-only Level-1 means are
0.142809M prompt and 0.021233M completion tokens over eleven verified tasks;
the failed depthwise task's 332,130 tokens remain in cohort totals. Five of
the six independent model/language cohorts are still missing from that frozen
comparison. It adds no model, GPU or Lean experiment.

The [updated two-cohort comparison](results/full-shape-comparison-deepseek-flash-hip-v1/RESULTS.md)
adds the complete Flash HIP packet without changing the frozen initial report.
Flash verified nine of twelve Level-1 and three of five Level-2 tasks. Its
success-only mean prompt/completion costs are 0.081640M/0.005264M and
0.120210M/0.005286M tokens respectively. Four of six independent model/language
cohorts remain missing; this is not a paper-completion denominator. All failed
tasks remain in spending totals. The comparison reruns no experiment.

The [updated three-cohort comparison](results/full-shape-comparison-three-cohorts-v1/RESULTS.md)
adds Flash CUDA and preserves both earlier frozen reports. Flash CUDA verified
five of twelve Level-1 and four of five Level-2 tasks. Its success-only mean
prompt/completion costs are 0.072328M/0.006827M and 0.106352M/0.005578M tokens,
with denominators five and four respectively. Three of six independent
model/language cohorts remain missing. All eight failed tasks remain in total
spending. This report adds no model, GPU or Lean experiment and supplies no
original-paper model result.

The [comparison publication receipt](results/full-shape-comparison-publication-v1/results.json)
checks its original eight public files over TLS without authentication. The
[comparison main receipt](results/full-shape-comparison-ci-main-v1/results.json)
and [Flash-runtime main CI record](results/full-shape-flash-runtime-main-ci-v1/results.json)
retain all nineteen successful exact-source CI jobs for those prior changes.

The [Flash HIP main receipt](results/full-shape-flash-hip-ci-main-v1/results.json)
also retains its checked non-force fast-forward and all nineteen successful
jobs on the actual resulting main commit. The
[bounded PTX implementation review](results/ptx-verifier-implementation-review-v1/results.json)
binds thirteen inspected `ptx_verifier` source/fixture files to their Git blobs
and records its explicit PTX CTA-zero analysis and exported-output proof
boundary. It establishes no whole-launch LARK bridge or new certificate.
The [fresh artifact check](../paper_results/original-artifact-refresh-20261113-0900/results.json)
records an empty KernelCraft endpoint, no releases and no repository search
matches for the exact paper ID; its separate official-arXiv observation showed
v1 only. These are bounded observations, with no author contact or assertion
that all possible artifact locations were searched.

The [full-size protocol](FULL_SHAPE_METHOD.md) now validates all seventeen
existing HIP benchmark shapes with four fixed proof slots. Its 17 SDK positive
controls and 17 missing-proof negatives passed under the fixed new Lean limits.
The recorded library-read controller checks four complete proof terms before
elaboration and independently rechecks successful candidates. Its preparation
controls are separate from model-generated proofs and the earlier reduced cohorts.
The [new pinned GLM runtime](results/full-shape-runtime-glm53-v1/results.json)
passes its recorded warmup and all seventeen initial context checks. Every cached
checkpoint file was rehashed. The largest initial prompt uses 22,489 tokens
within the common 65,536-token limit. The
[full-size ReLU pilot](results/full-shape-pilot-glm53-v1/binding.json) verified its
first proof submission after three library reads. All four requests and two
fresh Lean checks are archived: 36,503 prompt and 1,064 completion tokens.
This single pilot is separate from the seventeen-task cohort, which is still
running. The [recorded-protocol replay](results/full-shape-pilot-replay-v1/binding.json)
binds all four requests to the fixed tasks and source reads, then checks the
existing successful model proof in two more fresh Lean processes. It adds no
model calls, model trial or registered source certificate.

The [new DeepSeek runtime](results/full-shape-runtime-deepseek-v1/results.json)
rehashes all 48 cached weight files and 31 support files, passes a separate
69-token warmup, and fits all seventeen initial prompts. Its largest uses
22,979 input tokens within the same 65,536-token budget. The full DeepSeek
cohort is complete above; setup receipts remain separate from its proof results.
All eighteen
exact-source CI jobs passed before the checker, preparation and original pilot
were [fast-forwarded to main](results/full-shape-source-ci-main-v1/results.json).

The [Flash HIP runtime](results/full-shape-runtime-flash-hip-v1/results.json) and
separate [Flash CUDA-task runtime](results/full-shape-runtime-flash-cuda-v1/results.json)
use two GPUs each and the same pinned checkpoint and inference settings.
Each passed a separate 31-token non-proof warmup and all seventeen initial
context checks, with largest prompts of 22,489 and 22,496 tokens respectively.
Both reuse the same recorded revalidation of 62 weight files and nine support
files. The packets retain every warmup/tokenizer request and response, serving
configuration and exact controller. Their prompts were regenerated from the
frozen tasks before publication. Setup claims no model proof successes or GPU
kernel trials; CUDA identifies the proof-task source language, without NVIDIA
execution evidence.

The [paired specification identity main receipt](results/hip-cuda-reference-identity-ci-main-v1/results.json)
records all nineteen exact-source CI jobs passing, including a fresh full
seventeen-pair identity study, before the checked non-force main fast-forward.

This is an **independent proof-slot experiment**, not the paper's original agent
harness, kernels, model endpoints or reported pass rates/token costs. Real model
responses, including unsuccessful attempts, are archived separately from client
integration tests that use an explicit stub.

The [17-fixture comparison audit](COMPARISON_METHOD.md) reconstructs complete
request histories, separates first attempts from retries, and reruns every
model-generated certificate. Its [completed three-model result](results/model-comparison-20261109/README.md)
records one first-attempt certificate for GLM and zero for Flash/DeepSeek;
DeepSeek's later-retry certificate remains separate.

[DeepSeek-V4.1-Flash-1017 runtime and completed pilot](results/runtime-deepseek-20261109/)
now include 48 hash-checked weight shards, 31 supporting files, a healthy TP=4
MI350X endpoint and real requests/responses. Nine baseline requests across ReLU,
SiLU and Softmax used 84,360 prompt and 147,456 completion tokens. All completion
tokens were reported as reasoning: **zero final proofs and zero Lean checks**.
A separate 32,768-token ReLU probe also returned no final proof. These are
reasoning-only outcomes, not Lean proof rejections or the paper's pass rates.

The first owned DeepSeek container failed before inference because an optional
INT4 QuickAllReduce implementation lacked its expected `compile` method. The
archived v2 launcher uses standard RCCL collectives; checkpoint/image pins remain
the same. `serve_deepseek.py` matches that successfully executed v2 launcher.
Two successful `LARK_READY` warmups are protocol checks, not proof successes.

A separate `--thinking-token-budget 4096` variant reserves output room for final
answers. It is explicitly recorded in requests/reports and differs from the
baseline. Its [completed DeepSeek pilot](results/pilot-deepseek-budget4096-20261109/summary.json)
returned actual candidates: eight Lean checks were unproved and one proposal was rejected by the proof-slot validator;
no certificates verified in those first three cases.

The [expanded DeepSeek cohort](DEEPSEEK_RESULTS.md) has now completed all 17
reduced families at the same settings: **one depthwise-convolution certificate
verified**, 37 actual Lean checks, 14 proposal-validation rejections, and 821,063
reported tokens across 51 requests. Its successful exported tactics match the
model response and passed another independent workspace recheck. This is a
reduced-fixture result, not the paper's original pass rate or full-size kernel.

The [GLM-5.3-Flash budget variant](results/pilot-glm-flash-budget4096-20261109/summary.json)
initially completed three cases. Its [expanded 17-fixture cohort](results/model-comparison-20261109/README.md)
is now complete: 17 requests, seven unproved Lean checks, ten invalid proposals,
312,772 reported tokens and no certificates. A fresh two-model audit confirms
the same first-request messages as DeepSeek on every fixture. Both models have
zero first-attempt certificates; DeepSeek's later success remains separate from
the one-request Flash budget.

[Full GLM-5.3 ran successfully](results/runtime-glm53-20261109/summary.json) on GPUs
0/1/6/7, TP=4, using the pinned native FP8 checkpoint. All 141 weight shards and
eight supporting files passed independent validation. Its successful protocol
warmup used 22 prompt and five completion tokens; this is not proof evidence.
The [completed three-case batch](results/model-comparison-20261109/glm53-budget4096-remote/results.json)
used seven requests and 124,057 reported tokens, with one SiLU certificate and
five actual Lean checks. ReLU and Softmax remained unproved within their
recorded budgets. Both additional seven-case batches have finished. Across all
17 fixtures, GLM used 49 requests, 832,937 reported tokens and 36 Lean checks,
with one first-attempt SiLU certificate and no additional certificates after retries.

Its first [completed SiLU case](results/model-comparison-20261109/README.md)
contains a real model-generated proof whose exact tactics, immutable first
request and fixture bytes were checked before another successful local Lean
recheck. The complete cohort audit now includes every unsuccessful case as well.
Its [lifecycle record](results/model-comparison-20261109/progress/glm53-lifecycle-stopped.json)
records a clean stop of the owned service after all work completed. The separate
[comments-only DeepSeek replay](COMMENT_REPLAY_RESULTS.md) made no model calls;
both transformed candidates remained unproved and the raw counts are unchanged.

The checkpoint lives in two owned RAM-backed directories, with at least 32 GiB
reserved on each filesystem. `download_ranges.py` checks ranges and whole-file
SHA-256; `checkpoint.py` independently validates the snapshot. `serve_glm.py`
matches the successfully executed four-GPU launcher. The sequence archived
completed runs and stopped only the exact owned DeepSeek/old Flash container IDs
before launching full GLM. No other services were stopped.

The [completed low-effort Flash pilot](GLM_FLASH_RESULTS.md) has nine responses:
eight reasoning-only and one unproved Lean check, with 231,592 reported tokens.
The three first requests exactly match the reasoning-budget variant after
removing its added budget field; the audit preserves their distinct retry counts.
The original runtime on GPUs 6/7 is stopped. A separate owned Flash runtime on
GPUs 2/3 completed the additional 14 reduced fixtures, one request each. It was
stopped after both controllers exited and active/waiting request gauges reached
zero; its exact identity and clean exit are archived. Earlier [runtime records](results/runtime-20261109/)
remain historical inference evidence, not a proof success. Hosted API spending
is zero; original paper pass rates are not claimed.

The [initial 600-second pilot](results/pilot-600s-20261109/summary.json) was
interrupted after its first request timed out and a retry had started. Both
attempts and the intervention are archived, with unknown token usage; neither
returned a proof or reached Lean. This is transport/incomplete-run evidence,
with zero proof rejections. All three pilot cases were rerun with an explicit 1,800-second request timeout;
the completed rerun and original failure are both retained.

The [max-effort follow-up](results/pilot-max-20261109/summary.json) returned one
complete response: 7,719 prompt tokens plus 16,384 reasoning tokens, with no
final proof content. It never reached Lean. Its identical-budget retry was
interrupted and preserved. The completed `--reasoning-effort low` pilot used the same seed and 16,384-token
cap; its first ReLU messages match the max-effort request exactly. This effort variant differs from the paper's GLM
settings and is not an original pass-rate result.

Three named model families have official ungated weights. Metadata was checked
on 2026-11-09; revisions are pinned in `checkpoint.py`:

| Checkpoint | Weight GiB | Revision |
| --- | ---: | --- |
| [GLM-5.3-Flash](https://huggingface.co/zai-org/GLM-5.3-Flash) | 305.79 | `46a050bec13002ad29ee795c16e61cf4fa3c4a9c` |
| [GLM-5.3](https://huggingface.co/zai-org/GLM-5.3) | 703.74 | `ba32f8c19c8738e2c57c71798c601d477a7bf844` |
| [DeepSeek-V4.1-Flash-1017](https://huggingface.co/deepseek-ai/DeepSeek-V4.1-Flash-1017) | 475.25 | `1bae0e1088993b9b82de08f59de5be5a34e42170` |

The paper's experiment configuration names the **1017** DeepSeek update. The
unmodified launch checkpoint is a different model revision. Weight sizes are
downloaded file sizes, not peak serving-memory estimates.

## Prepared GLM-5.3-Flash configuration

The prepared launcher uses the official native FP8 checkpoint, two MI350X GPUs,
TP=2, 131,072-token context, at most two sequences and eager execution. The model
is served from local files with Hugging Face/Transformers offline mode enabled.
Only `127.0.0.1:19081` is published on the host. A named existing container or
occupied port causes a refusal; existing services are never stopped.

The pinned official ROCm image is
`vllm/vllm-openai-rocm@sha256:71a5d125b10a594752014b917a00cb1743387d1be9ee188aa1862af0b143c7dd`.
Its recorded versions are vLLM `0.33.0rc1.dev1065+g083fbac02`, PyTorch
`2.13.0+rocm10.0.0`, HIP `7.15.26333`. A tensor smoke test passed on MI350X.
The configuration follows the [official model recipe](https://github.com/vllm-project/recipes/blob/main/models/zai-org/GLM-5.3-Flash.yaml).
Numeric host group IDs are used because the image lacks a named `render` group.

`mi350` reports 252 GiB per GPU and sufficient free RAM for a checkpoint cache
under `/dev/shm`. Its small remaining disk space motivates keeping weights and
compiler caches in RAM. This storage is ephemeral. `mi350-2` has one GPU and
does not fit the unmodified Flash checkpoint with this configuration.

## Commands

Read-only preflight from the repository checkout:

```bash
python reproduction/local_models/preflight.py --host mi350 --output /tmp/lark-preflight.json
```

On the GPU host, with standard-library Python and `huggingface_hub==1.0.0`:

```bash
export HF_HOME=/dev/shm/lark-models
python checkpoint.py --cache "$HF_HOME/hub" --output /tmp/lark-checkpoint.json
python serve.py --checkpoint /tmp/lark-checkpoint.json --cache "$HF_HOME/hub" \
  --runtime-cache /dev/shm/lark-runtime-cache --output /tmp/lark-server.json \
  --gpu-ids 6,7 --launch
python ready.py --server /tmp/lark-server.json
```

`checkpoint.py` checks each downloaded safetensors file's length and SHA-256
against its pinned Hugging Face LFS metadata. `serve.py` requires this completed
record and checks selected GPUs/port before launching. `ready.py` checks the
owned container, health endpoint and served model identity without model calls.

Run the proof controller directly on the GPU host from a checkout/source snapshot
that includes `lark_kernels`, the Lean model and fixtures. This avoids an SSH
forward becoming the transport dependency for a long request. Lean 4.19.0 must
be available on that host. For an interactive local controller, a separately
maintained SSH forward is an alternative:

```bash
ssh -N -L 127.0.0.1:19081:127.0.0.1:19081 mi350
python reproduction/local_models/run.py \
  --url http://127.0.0.1:19081/v1/chat/completions \
  --model zai-org/GLM-5.3-Flash --server-record /tmp/lark-server.json \
  --case reproduction/nonlinear/cases/float16/relu \
  --case reproduction/nonlinear/cases/float16/silu \
  --case reproduction/nonlinear/cases/float16/softmax \
  --output /tmp/lark-local-proof-study --lean /path/to/lean-4.19.0/bin/lean \
  --model-timeout 1800 --reasoning-effort low --thinking-token-budget 4096
```

## Experiment boundary

The client accepts explicit loopback HTTP endpoints only, disables proxies and
redirects, and sends no API keys. Requests/responses, hashes, reported token
usage and timings are preserved. Hosted API charges are zero; GPU time and
electricity are not estimated. Transport failures, invalid proposals, unproved
checks and verified certificates have separate outcomes. Unknown token usage is
flagged instead of being inferred from text.

Models receive fixed Lean source and return bounded JSON tactics/segments.
They receive no shell, tools, editable theorem statements or editable GPU
sources. A successful proposal must pass Lean, the actual axiom audit, a fresh
certificate export and source-binding recheck. The fixture program and reference
remain independently pinned. No model-generated diagnosis is accepted as proof.

Default pilot settings are three requests per case, seed 261102028, temperature
zero, 16,384 generated tokens per request, 600-second request timeout and
150-second Lean timeout. GLM reasoning effort is `max`, as the model card
recommends for benchmarks. These budgets and this bounded harness differ from
the paper's multi-agent loops, original registry, restart/review policies and
API billing. Any resulting measurements must remain labeled as adaptations.

`checkpoint.py --local-only --wait-timeout 7200` validates an existing snapshot
while another downloader atomically completes missing files. It fetches pinned
file metadata over HTTPS and makes no model calls or weight downloads. Every
weight needs its official LFS SHA-256; configuration/tokenizer/support files are
checked against their LFS digests or Git blob IDs, with SHA-256 also recorded.
The readiness record cannot become `verified-download` until all selected files
pass these checks. Same-length altered weights or configuration files are refused.

The [paired reference publication receipt](results/hip-cuda-reference-identity-publication-v1/results.json) verifies all four packet files (249,551 bytes) against their immutable public Git blobs over TLS without authentication. The [DeepSeek main receipt](results/full-shape-deepseek-ci-main-v1/results.json) records its checked, non-force fast-forward after all eighteen source CI jobs passed. These receipts add no model, GPU or numerical trials.

The [Flash runtime publication receipt](results/full-shape-flash-runtimes-publication-v1/results.json) verifies both complete setup packets and the reference identity main receipt: thirteen files, 770,126 bytes, downloaded anonymously over TLS and matched to their immutable Git blobs. It adds no model or proof trials.
