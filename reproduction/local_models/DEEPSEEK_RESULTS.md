# Independent DeepSeek proof-proposal cohort

Run date: 2026-11-09. **This is not the paper's original model experiment.**
[Audited summary](results/pilot-deepseek-expanded-20261109/cohort-summary.json),
[three-case batch](results/pilot-deepseek-budget4096-20261109/),
[fourteen-case batch](results/pilot-deepseek-expanded-20261109/).

**1 of 17 reduced HIP fixtures verified within three requests per case.**
The successful reduced depthwise-convolution proposal passed the proof-slot
validator, Lean, a fresh certificate export and independent rechecks on the GPU
host and the primary workspace. Its exported tactics match the model's actual
final response; kernel/reference/task bytes match the frozen fixture. The
certificate proves this reduced task, not the original production or full-shape
kernel. The separate full-shape certificates use pinned human-developed lemmas.

| Reduced family | Requests | Outcome |
| --- | ---: | --- |
| batchmatmul | 3 | unproved |
| conv2d | 3 | unproved |
| depthwise_conv | 3 | verified |
| ffn | 3 | unproved |
| flash_attn | 3 | unproved |
| gelu | 3 | unproved |
| gemm | 3 | unproved |
| gemv | 3 | unproved |
| gqa | 3 | unproved |
| layernorm | 3 | invalid-proposals |
| linear | 3 | unproved |
| relu | 3 | unproved |
| rmsnorm | 3 | unproved |
| rope | 3 | unproved |
| silu | 3 | unproved |
| softmax | 3 | unproved |
| swiglu | 3 | unproved |

The two disjoint batches share model revision `1bae0e1088993b9b82de08f59de5be5a34e42170`, TP=4,
seed 261102028, temperature 0, at most 16,384 output tokens, and a 4,096-token
reasoning limit. Every request/response and actual Lean check is archived.

- 51 requests and 51 responses.
- 37 actual Lean checks; proposal-validation rejections are counted separately.
- 602,341 reported prompt tokens + 218,722 completion tokens = **821,063** total.
- **$0 hosted API spending**; local GPU time/electricity are not priced.

An uncertified proposal says the model did not prove the task in this harness
and budget. It does not say the kernel is buggy; deterministic certificates
already exist for all these reduced fixtures. The original models' registry,
agent tools, restart/review policies and stage traces are unavailable. Our
three-slot request combines obligations rather than reproducing the original
segmentation/equivalence agents or their forty-check budgets.

The earlier unbounded-reasoning pilot returned nine reasoning-only responses
and no Lean checks; its 32,768-token follow-up also returned no proof. Those
[different-budget runs](results/runtime-deepseek-20261109/) remain separate from
this cohort. `summarize_deepseek.py --lean /path/to/lean` audits both batches,
checks proposal provenance and reruns every successful certificate.
