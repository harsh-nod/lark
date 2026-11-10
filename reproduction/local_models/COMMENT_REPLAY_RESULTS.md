# Comments-only replay of refused candidates

This independent CPU experiment tests one restriction of the local proof-slot
harness. It is not the paper's original failure-analysis ablation, a new model
cohort or a replacement for the [recorded comparison](COMPARISON_METHOD.md).
No model calls were made and no raw responses or baseline counts were changed.

Of DeepSeek's 14 invalid proposals, two first-attempt proposals contain comments:
LayerNorm and RMSNorm. Their exact decoded segmentation and proof slots were
recovered from the archived responses after auditing the full original cohort.
The replay masks recognized comments with whitespace, preserves all remaining
code and segmentation, then uses the unchanged proof validator and Lean checker.

| Recorded candidate | Comments removed | Actual Lean replay | Verified / independently rechecked |
| --- | ---: | --- | ---: |
| LayerNorm, first attempt | 9 | unproved | 0 |
| RMSNorm, first attempt | 3 | unproved | 0 |

There were two actual replay checks, zero timeouts and zero accepted certificates.
Lean reported failed `rfl` tactics at the segmentation and launch-completion
obligations. These are failed proof scripts, not proof that the fixed kernels or
the obligations are false. Removing comments alone did not produce a certificate.
No tactics, segments, statements or kernel/reference code were repaired.
DeepSeek's raw result remains one verified certificate within its three-request
budget, with zero first-attempt certificates across the 17 fixtures.

The transformation deliberately accepts only ordinary line comments and nested
block comments with ASCII text and no tabs. Quoted forms, isolated carriage
returns and documentation-comment tokens are refused. Documentation comments
are actual tokens in the pinned [Lean 4.19 parser](https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Parser/Basic.lean#L479),
so treating them as generic whitespace would be inappropriate. `native_decide`,
admissions and declarations outside comments remain forbidden. Seven parser and
policy controls passed, including nested comments, quoted markers, forbidden
code outside comments and preservation of line structure.

[Completed results](results/comment-replay-deepseek-20261109/results.json),
[manifest](results/comment-replay-deepseek-20261109/manifest.json) and per-candidate
exports retain the original and normalized proposals, exact Lean statements,
unproved reports and logs. Each source response/request is bound by its original
hash; the baseline was freshly audited, including its existing successful proof.
The [validation record](results/comment-replay-deepseek-20261109-validation.json)
also binds the implementation snapshot and test log.

```bash
python3 reproduction/local_models/replay_comments.py --model deepseek \
  --output /tmp/deepseek-comments-replay --lean /path/to/lean-4.19.0/bin/lean
```

The command requires finished raw cohorts, a fresh output directory and Lean.
It does not estimate counterfactual interactive histories or token costs. The
raw model comparison and original-paper coverage ledger remain separate.
