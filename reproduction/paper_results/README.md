# Audit of every paper table and figure

[Updated frozen ledger](snapshots/20261110-v17/results/RESULTS.md) ·
[earlier v16 ledger](snapshots/20261110-v16/results/RESULTS.md) ·
[historical ledger](results/RESULTS.md) · [historical audit](results/audit.json)

The original paper is **not fully reproduced**. This audit inventories all 17
tables and seven outer figure groups in the arXiv v1 preprint, plus 16 narrative
anchors for results and implementation requirements that a table-only checklist
would miss. Configuration tables and method diagrams are identified separately
from measurements. Overlapping items do not define a completion percentage.

The [updated snapshot](snapshots/20261110-v17/results/RESULTS.md) includes the later
production SiLU, exact-real, full-wave reduction and complete native weighted
RMSNorm studies at experiment-code commit `489b836`. Its evidence and auditor are frozen for replay without a
historical checkout, and its existing-study links target that exact Git commit:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261110-v17 \
  --source-archive /path/to/2611.02028v1.tar
```

The [validation records](snapshot-v17-validation/results.json) include replay
outside the checkout with Git unavailable, two fully rehashed false-completion
claims, a fully rehashed traversal entry and a wrong-manuscript control. Repeat
them with a fresh output directory:

```bash
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261110-v17 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-snapshot-controls
```

The remainder of this page documents the original historical snapshot.

This is a coverage snapshot of the evidence associated with experiment-code
commit `b5fb165`. Later independent studies, including the
[small upstream-derived activation adaptation](../production_activation/RESULTS.md),
are tracked in the [current coverage ledger](../COVERAGE.md). The snapshot is not
retroactively relabeled as original-paper reproduction.

The check below must run from audit commit
`904b0e729625e3f072e417adcfa440a9318b3b4e` because it binds the documentation
and evidence files at that historical snapshot. Later coverage updates change
some of those bytes. Create a separate checkout before checking the snapshot:

```bash
git worktree add --detach /tmp/lark-paper-audit-snapshot \
  904b0e729625e3f072e417adcfa440a9318b3b4e
cd /tmp/lark-paper-audit-snapshot
```

The archive hash, its 47 member-file hashes, the preprint input order, every
float's source label/location, and the selected published evidence hashes are
recorded. The target interpretations and missing-input assessments are authored
judgments in [targets.json](targets.json), not conclusions established by file
hashes. Existing experimental validation remains in each linked study; this
audit performs no new Lean check, GPU execution or model call.

The final experiment-code CI run at `b5fb165` passed. Its run/job API responses
are preserved here, and the linked local validation records all 124 tests.
The expanded artifact search records read-only commands and responses. It found
no original release at the inspected endpoints; this is not an exhaustive claim
about all authors, branches, unindexed files or future releases.

To reconstruct the audit, download the original source archive from
<https://arxiv.org/src/2611.02028v1>. Its required SHA-256 is
`095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2`.
The auditor reads archive members without extracting them and is deliberately
specific to this manuscript's preprint/appendix flags, not a general TeX engine.

```bash
python3 reproduction/paper_results/audit.py \
  --source-archive /path/to/2611.02028v1.tar \
  --output reproduction/paper_results/results --check
```

Omit `--check` and choose a new output directory to write another audit. The
generated Markdown links are relative to the chosen output directory.

The exact original kernels, mutants, production adaptations, model dialogues,
stage costs and supplementary GQA project remain missing inputs. Original H100
measurements require NVIDIA hardware. Historical development effort cannot be
regenerated independently. Broader optimized/tiled/online kernel support also
remains software work; all independent AMD evidence keeps its narrower scope.
