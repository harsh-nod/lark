# Independent 17-fixture comparison audit

The completed DeepSeek cohort and the running GLM/Flash cohorts use the same
17 reduced HIP fixtures, seed 261102028, temperature zero, 16,384 output-token
cap and 4,096 reasoning-token limit. These are independent experiments, not
the original paper's registry, kernels, agents, budgets or pass rates.

`compare_models.py` audits recorded data without making model calls. The
combined three-model result remains incomplete until all required batches
have finished and their evidence is archived locally.

```bash
# The completed DeepSeek data can already be audited independently:
python3 reproduction/local_models/compare_models.py --model deepseek \
  --output /tmp/deepseek-comparison-audit --lean /path/to/lean-4.19.0/bin/lean

# After all additional cohort archives arrive, omit --model to audit all three:
python3 reproduction/local_models/compare_models.py \
  --output /tmp/three-model-comparison --lean /path/to/lean-4.19.0/bin/lean
```

The all-model command refuses missing or unfinished evidence. A single-model
audit explicitly records `three_model_comparison_complete:false`; it cannot
establish a cross-model request match. Expected paths, checkpoints, image,
parallelism and per-case request budgets are in the script's `COHORTS` table.

The audit checks:

- Exactly the same 17 fixtures once per model, including unsuccessful cases.
- Kernel, reference and task bytes against the frozen fixture hashes.
- Every request's complete Lean statement, program, previous proposal and
  feedback reconstructed independently from the fixture and preceding attempt.
- Request/response hashes, pinned local endpoint/checkpoint/image, source-run
  completeness, actual Lean checks and token accounting.
- Every successful exported proposal against the model's actual final response,
  followed by a fresh source-bound Lean recheck. A mathematically valid manual
  replacement is refused as evidence of model authorship.
- Identical decoded first-request messages across selected models. Tokenizers,
  templates, native precision and tensor parallelism still differ, so this is
  not an isolated measurement of model size.

Only first attempts are compared across models. DeepSeek/full GLM allow up to
three requests per case; Flash allows one in this cohort. Later-retry successes
are reported separately and never promoted to first-attempt successes.
Transport failures, empty final responses, invalid proposals and unproved Lean
checks retain distinct outcomes. Missing total or reasoning-token usage stays
explicitly incomplete rather than being treated as zero known consumption.

Proposal-refusal channels and literal `native_decide`/comment markers describe
the bounded harness's validator. They are not kernel-bug diagnoses, original
mutation channels, or proof that a refused candidate could never work. In the
completed DeepSeek data, 12 of 14 invalid proposals contain `native_decide` and
two contain comment markers; these lexical restrictions are part of our harness.
Raw responses remain unchanged, and no posthoc tactic repair is included in
the comparison counts.

The comparison JSON binds the audited source files and independent recheck logs.
It always retains `original_paper_fully_reproduced:false`. The [coverage ledger](../COVERAGE.md)
separates original dependencies from these adaptations.

Once all three cohorts pass the audit, the report/figure command is:

```bash
# Requires optional matplotlib, in addition to the standard-library auditor:
python3 reproduction/local_models/render_comparison.py \
  --audit /tmp/three-model-comparison --output /tmp/three-model-report \
  --lean /path/to/lean-4.19.0/bin/lean
```

The renderer refuses a partial cohort before creating its output. It rebuilds
the complete audit from raw requests/responses and freshly rechecks positive
certificates before accepting the summary's counts. The figure compares only
common first attempts; a separate table retains the different retry budgets.
Unknown token usage is labeled incomplete and omitted from token bars.
The output manifest binds the Markdown, SVG, new recheck logs, input audit and
renderer source. No combined result or figure is currently claimed from the
unfinished cohorts.
