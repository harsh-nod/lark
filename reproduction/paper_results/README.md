# Audit of every paper table and figure

[Updated frozen ledger](snapshots/20261112-v22/results/RESULTS.md) ·
[earlier v21 ledger](snapshots/20261112-v21/results/RESULTS.md) ·
[earlier v20 ledger](snapshots/20261112-v20/results/RESULTS.md) ·
[earlier v19 ledger](snapshots/20261111-v19/results/RESULTS.md) ·
[earlier v18 ledger](snapshots/20261110-v18/results/RESULTS.md) ·
[earlier v17 ledger](snapshots/20261110-v17/results/RESULTS.md) ·
[earlier v16 ledger](snapshots/20261110-v16/results/RESULTS.md) ·
[historical ledger](results/RESULTS.md) · [historical audit](results/audit.json)

The original paper is **not fully reproduced**. This audit inventories all 17
tables and seven outer figure groups in the arXiv v1 preprint, plus 16 narrative
anchors for results and implementation requirements that a table-only checklist
would miss. Configuration tables and method diagrams are identified separately
from measurements. Overlapping items do not define a completion percentage.

The v22 snapshot freezes **3,378 published evidence files** at commit `e7ea523`,
plus its auditor and targets. It incorporates the independent CPU reference
studies: 240 sampled production outputs across twelve variants and 340 sampled
benchmark outputs across seventeen families, each using four input strata.
The benchmark study also checks all 589,824 recorded attention scores. Fresh
source replays reproduce the sampled values and scores bit-for-bit; source-checked
SDK import caches were reused. The numerical studies add no formal certificates,
GPU trials, model calls or universal floating-point guarantees.

The new auditor checks the complete case/stratum rosters, sampled values and bit
representations, score counts, resource limits, proof scope, fresh-replay claims
and anonymous-publication receipts. It checks frozen report consistency without
rerunning Lean or the study packets' stricter raw-data validators. Large numerical
archives remain in the separately linked immutable study packets. The snapshot
also applies the explicit v21 semantics correction below; all older snapshots
retain their original bytes. The original registry, reference formalizations,
model/token histories and NVIDIA measurements remain missing inputs.

Replay the snapshot or repeat its controls with fresh output directories:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261112-v22 \
  --source-archive /path/to/2611.02028v1.tar
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261112-v22 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-v22-controls
```

The [v22 validation](snapshot-v22-validation/results.json) passes two positive
replays outside Git and rejects **24 negative controls**, including sixteen
new numerical-report mutations. Changed inner receipt hashes, archive hashes,
provenance and outer manifests are synchronized; rejection must reach the named
semantic consistency gate. The
[v21 compatibility check](snapshot-v22-v21-compatibility/results.json) also
repeats its unchanged eight controls with the updated reader. These records
are separate from the frozen snapshot and the experiments it cites. The
[anonymous publication check](snapshot-v22-publication/results.json) downloaded
eleven files totaling 39,282,190 bytes from `4f647f9`, matched every committed
byte with TLS verification enabled, and repeated both positive replays and all
24 controls outside Git. The
[CI/main receipt](snapshot-v22-ci-main-v1/results.json) records all eighteen
jobs passing at source `4f647f9` and the checked non-force remote/local
fast-forward to `1da8a64`. The intervening merge and publication changes contain
documentation and recorded receipts; SDK, Lean, tests, workflows, ledger readers
and frozen snapshots remain identical to the tested source.

**v21 correction:** the frozen `dependencies.semantics` paragraph mistakenly
retains an older statement that FlashInfer, SGLang RMSNorm and AWQ are
unimplemented. Its own production inventory and source/replay checks correctly
record their completed independent profiles. The
[explicit correction](errata/20261112-v21-semantics.json) replaces that authored
assessment; the frozen snapshot, proof sources and experimental results remain
unchanged. General instruction/signature coverage and the original artifacts
are still separate gaps.

The [v21 snapshot](snapshots/20261112-v21/results/RESULTS.md) freezes 3,312
published evidence files at commit `3eab929`, plus its own auditor and targets.
It adds complete distinct FlashInfer RMSNorm, guarded packed SGLang RMSNorm
and native FP16 single-split-K AWQ GEMM to the earlier studies. Each new
profile has four source-bound exports and rechecks, complete initialized
launch execution, actual whole-trace race freedom, output extraction and dense
canonical-real equality. Their standalone source-only replays reproduce 522,
782 and 734 axiom-audit occurrences over 68, 88 and 83 owned modules respectively.
Installed-package and anonymous source-download checks also pass. CI records
retain their exact source commits and observation times; the AWQ publication
receipt captured the new 18-job CI run while it was still in progress.

A ten-case production inventory is checked against the manuscript table.
Nine accepted families and the rejected original softmax race case have
independent scoped coverage. Their separate fixed profiles publish 48 exports;
these are not the authors' nine original certificates. Softmax retains its
development-checker scope and zero registered frontend source certificates.
The SGLang lane-zero repair and original unguarded conflict are explicit.
Paired AMD measurements retain their floating-point differences, separately
from the idealized real proofs. No original experimental row is relabeled reproduced.
The evidence and auditor are frozen for replay without a historical checkout,
and study links target that exact Git commit:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261112-v21 \
  --source-archive /path/to/2611.02028v1.tar
```

The [validation records](snapshot-v21-validation/results.json) include replay
outside the checkout with Git unavailable and eight rejected controls: global
and original-result completion, a false AWQ certificate count, omission of
AWQ from the manuscript inventory, rehashed study-level IEEE/cache claims,
an unsafe archive path and the wrong manuscript.
All but the wrong-manuscript control fully rehash the changed packet. Repeat
them with a fresh output directory:

```bash
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261112-v21 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-snapshot-controls
```

The [v20 compatibility check](snapshot-v21-v20-compatibility/results.json)
replays the unchanged prior snapshot and repeats all six of its original
controls. The new AWQ control only changes when the selected snapshot actually
contains complete AWQ certificates. The refreshed
[bounded artifact search](original-artifact-refresh-20261112-v21/results.json)
records primary pages, named repository metadata/head and three limited queries;
it does not establish absence from other repositories, branches or future releases.

The [public-download replay](snapshot-v21-publication/results.json) anonymously
downloaded all eleven snapshot/reader files from commit `5a3cd45`: 38,506,592
bytes, each matching its committed source. The downloaded tools repeated the
outside-checkout replay with Git unavailable and all eight negative controls.
The ledger and its controls perform no fresh Lean checks, model calls or GPU
trials; linked experiments retain their own validation and limits.

The [complete ledger CI/main receipt](snapshot-v21-ci-main-v1/results.json)
records all eighteen jobs passing for source `5a3cd45` and the checked
fast-forward of `main` to publication commit `b934b02`. The intervening changes
are documentation and recorded evidence; SDK, Lean, tests, configuration and
workflow sources are unchanged. Earlier frozen observations retain their actual
timestamps and are not rewritten as later CI success.

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
