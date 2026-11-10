# Offline local-model experiments

This is an **independent proof-slot experiment**, not the paper's original agent
harness, kernels, model endpoints or reported pass rates/token costs. Real-model
proof results have not yet been recorded here. Client integration tests use an
explicit stub and are not model evidence.

GLM-5.3-Flash is now running on MI350X GPUs 6/7. Its 62 weight files and nine
supporting files passed pinned-content checks; the loopback endpoint passed
health/model checks. [Runtime records](results/runtime-20261109/) include one
real warmup request/response: 28 prompt tokens and 64 reasoning tokens, ending
at the 64-token cap with no final answer. This is inference evidence, not a proof
success. A separate three-case proof pilot is in progress. Hosted API spending
is zero; no original paper pass rate is claimed.

The [initial 600-second pilot](results/pilot-600s-20261109/summary.json) was
interrupted after its first request timed out and a retry had started. Both
attempts and the intervention are archived, with unknown token usage; neither
returned a proof or reached Lean. This is transport/incomplete-run evidence,
with zero proof rejections. All three pilot cases are being rerun with an
explicit 1,800-second request timeout; the original failure is retained.

The [max-effort follow-up](results/pilot-max-20261109/summary.json) returned one
complete response: 7,719 prompt tokens plus 16,384 reasoning tokens, with no
final proof content. It never reached Lean. Its identical-budget retry was
interrupted and preserved. A separate `--reasoning-effort low` pilot is now
running at the same seed and 16,384-token cap; its first ReLU messages match the
max-effort request exactly. This effort variant differs from the paper's GLM
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

After copying the readiness record locally, open an SSH forward in a separate
terminal and run the experiment from the repository root:

```bash
ssh -N -L 127.0.0.1:19081:127.0.0.1:19081 mi350
python reproduction/local_models/run.py \
  --url http://127.0.0.1:19081/v1/chat/completions \
  --model zai-org/GLM-5.3-Flash --server-record /tmp/lark-server.json \
  --case reproduction/nonlinear/cases/float16/relu \
  --case reproduction/nonlinear/cases/float16/silu \
  --case reproduction/nonlinear/cases/float16/softmax \
  --output /tmp/lark-local-proof-study --lean /path/to/lean-4.19.0/bin/lean
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
