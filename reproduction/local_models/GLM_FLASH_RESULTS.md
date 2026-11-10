# Independent GLM-5.3-Flash proof pilots

Run date: 2026-11-09. **No original-paper pass-rate claim.**
[Baseline receipts](results/pilot-glm-flash-low-20261109/),
[reasoning-budget variant](results/pilot-glm-flash-budget4096-20261109/),
[matched-request audit](results/pilot-glm-flash-low-20261109/budget-comparison.json).

The low-effort baseline completed nine requests across three reduced HIP fixtures:
**eight reasoning-only responses, one unproved Lean check, zero certificates**.
Reported usage was 84,888 prompt + 146,704 completion = **231,592 total tokens**.
This replaces the earlier in-progress status without discarding the interrupted
600-second/max-effort/SSH-forward failure records.

A separate 4,096-reasoning-token variant made one request per fixture, returning
one unproved Lean candidate and two invalid proposals. It used **50,976 reported
tokens** and verified no certificates. Invalid proposals are not Lean rejections.
Hosted API spending was **$0** in both runs; GPU time/electricity are not priced.

## Matched first requests

For each fixture the entire decoded request, including messages, model, seed,
temperature, output cap and reasoning effort, matches after removing the added
`thinking_token_budget:4096` field. Both runs used the same checkpoint, image
and ready runtime record. Compare only the first request in this table: later
baseline retries have different feedback and no matching variant retry.

| Reduced fixture | Baseline first outcome | Budgeted first outcome | Completion tokens: baseline / budgeted |
| --- | --- | --- | ---: |
| relu | no-proof-content | unproved | 16,384 / 4,478 |
| silu | no-proof-content | invalid-proposal | 16,384 / 14,970 |
| softmax | no-proof-content | invalid-proposal | 16,384 / 3,714 |

The budgeted requests returned final proposal content in these three cases;
none yielded a verified certificate. This is a small protocol/budget experiment,
not a statistical performance result or the authors' segmentation/failure-analysis
ablation. The original registry, tools, agent loop and stage costs are absent.
An uncertified attempt does not establish that the kernel is faulty.

An additional disjoint 14-fixture, single-request study is running on a separate
owned runtime with the same checkpoint/image/TP and budget, to complete the
17-fixture first-attempt comparison. It is not included in these completed counts.
`summarize_glm_flash.py` audits receipts and exact paired-request equality before
regenerating this report.
