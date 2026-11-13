# Audit of every paper table and figure

[Updated frozen ledger](snapshots/20261113-v25/results/RESULTS.md) ·
[earlier v24 ledger](snapshots/20261113-v24/results/RESULTS.md) ·
[earlier v23 ledger](snapshots/20261113-v23/results/RESULTS.md) ·
[earlier v22 ledger](snapshots/20261112-v22/results/RESULTS.md) ·
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

A separate [Level-2 cost-table arithmetic check](level2-cost-arithmetic-v1/RESULTS.md)
binds the original v1 source archive and checks all four displayed token means.
Opus's totals match the caption's successful-task rule at the displayed
precision. GLM's 373.90M input and 9.29M output instead match means over all
five tasks; the one successful task gives 71.90M/2.70M. This records a table/
caption discrepancy without deciding which the authors intended or recovering
any original model logs. Repeat the arithmetic without model or GPU calls:

```bash
python3 reproduction/paper_results/audit_level2_costs.py \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-level2-cost-check
```

The v25 snapshot freezes **3,623 evidence files** at commit `c61497b`, plus
its auditor and targets. Every earlier evidence member is preserved byte for
byte. The six full-size HIP/CUDA model cohorts retain 85 verified outcomes
across 102 tasks, 782 responses and 15,509,481 reported tokens under the fixed
adapted protocol.

The frozen auditor now checks three complete-source compiled FP16 PTX
development proofs: ReLU, GEMV and GEMM. GEMM covers the canonical
64x256 by 256x512 inputs and all 32,768 output lanes, every parsed instruction
and the actual sixteen-iteration backward loop, actual-trace race freedom,
extracted equality to the closed ordered-fold reference, and preservation of
memory outside the output allocation. Its four positive Main checks and
twenty fresh owned-module builds are repeated checks of one independent
kernel. Four direct Lean source-binding controls, isolated installed-wheel
replay, anonymous publication and all twenty-one actual source CI jobs at
`a2100f3` are retained. This abstract scalar proof retains its ABI, parsing,
pointer-layout and scalar-correspondence assumptions; it establishes no
universal IEEE guarantee or NVIDIA execution result.

Replay v25 without Git, SDK, Lean, model calls or GPU access:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v25 \
  --source-archive /path/to/2611.02028v1.tar
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v25 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-v25-controls
```

The [v25 validation](snapshot-v25-validation/results.json) passed all six
positive replays outside Git and rejected **65 negative controls** in 277.86
seconds. The [initial attempt](snapshot-v25-validation-timeout-v1/observer/results.json)
hit the unchanged 300-second aggregate cap and remains recorded as a failure.
The completed run schedules the same sixteen numerical controls with the
existing maximum of two independent replay workers; the 120-second per-replay
cap, 300-second aggregate cap, complete payload and every control remain.
The [validation history](snapshot-v25-validation/validation-history.json)
preserves both observations and executed sources. These are evidence replays,
with no new Lean checks, model calls or GPU experiments. The original registry,
optimized programs, harness, model histories, original mutants, broader PTX
coverage and H100/MI300X measurements remain unreproduced.

The [anonymous v25 publication check](snapshot-v25-publication/results.json)
downloaded all eleven source/snapshot files, totaling 88,810,099 bytes,
from commit `63aabf3` over verified TLS. Every byte matched the pinned Git
commit, and all six positive replays and 65 negative controls passed
outside Git. The [actual source CI record](snapshot-v25-source-ci-v1/results.json)
records all twenty-one jobs passing at that same source, including the
three-proof ledger, complete proof tests and GEMM export/replay job.
Only this README and recorded publication/CI receipts follow the tested
source; code, workflows, tests, Lean libraries and all snapshots retain
their exact tested bytes.

The earlier v24 snapshot freezes **3,565 evidence files** at commit `48aa4ae`, plus
its auditor and targets. It preserves all earlier evidence and all six independent
full-size model cohorts: 85 verified task outcomes across 102 tasks, 782 responses
and 15,509,481 reported tokens under the fixed adapted protocol.

Both exact-source compiled FP16 PTX development proofs are now checked by the
frozen auditor. ReLU covers 16,384 elements. GEMV covers all 119 instructions,
the actual 64-iteration backward loop and all 512 active lanes at the original
512x1024 development shape, with actual-trace race freedom and extracted-output
equality to a closed reference AST. Each kernel has four retained positive Main
checks and four direct Lean source-binding controls. The three positive rechecks
per kernel are repeated checks, not extra independent kernels or model successes.
Their actual source CI records contain nineteen ReLU jobs and twenty GEMV jobs.
The GEMV packet also retains anonymous publication, installed-wheel replay and
the checked main promotion. New bounded original-artifact observations are included.

Replay v24 without Git, SDK, Lean, model calls or GPU access:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v24 \
  --source-archive /path/to/2611.02028v1.tar
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v24 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-v24-controls
```

The [v24 validation](snapshot-v24-validation/results.json) passed all five
positive replays outside Git and rejected **57 negative controls**, including
all earlier controls and eight added fully rehashed GEMV claims. The complete
run took 260.74 seconds within the unchanged 300-second aggregate
limit. Each replay retains its 120-second cap, with at most two independent
replay workers. The control runner reuses compressed immutable members while
preserving every member and every changed byte in each independent control.
The [retained v23 compatibility run](snapshot-v24-v23-compatibility/results.json)
passed four positive replays and all 49 earlier controls in 260.22 seconds using
its recorded runner revision. Both receipts retain their exact executed sources
and logs. These are evidence replays, with no new model calls, Lean checks or
GPU experiments. The original paper remains incomplete; the registry, original
optimized programs and harness, model histories, full-size PTX coverage, closed-model
runs, original mutants and H100/MI300X timing cells remain missing.

The [anonymous v24 publication check](snapshot-v24-publication/results.json)
downloaded all eleven files, totaling 66,801,049 bytes, from source `a49569c`
with TLS verification enabled. Every byte matched the pinned Git commit, and
the downloaded snapshot passed all five positive replays and 57 negative
controls outside Git.
The [actual v24 source CI record](snapshot-v24-source-ci-v1/results.json)
records all twenty jobs passing at source `a49569c`, including raw six-cohort
regeneration, the frozen ledger controls and the complete proof-test job.
The subsequent publication/CI receipt commit changes only this README and
recorded receipts; source code, Lean libraries, tests, workflow definitions
and every frozen snapshot retain the exact tested source bytes.

The earlier v23 snapshot freezes **3,512 evidence files** at commit `44b414f`, plus its
auditor and targets. All six independent full-size HIP/CUDA model cohorts are
included: 85 verified proofs across 102 tasks, 782 recorded responses and
15,509,481 reported tokens. The auditor checks their complete rosters, fixed
protocol, successful-task token means, failed-task spending, accepted-Main and
recorded fresh-check bindings. Its six-of-six roster is not paper completion.

It also checks the separate exact-source compiled FP16 PTX ReLU proof packet:
one 16,384-element kernel, three positive rechecks and four direct Lean
source-binding controls. Source-only and isolated installed-wheel replay,
standard-axiom audits, anonymous publication and actual nineteen-job source CI
are recorded. These are repeated checks of one development proof; they add no
model success, registered legacy SDK profile or NVIDIA execution claim. The
full-size CPU compilation/assembly study and fresh bounded original-artifact
observations are frozen separately, with their original scopes preserved.

Replay v23 without Git, SDK, Lean, model calls or GPU access:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v23 \
  --source-archive /path/to/2611.02028v1.tar
python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v23 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-v23-controls
```

The [v23 validation](snapshot-v23-validation/results.json) passed four positive
replays outside Git and rejected **49 negative controls**, including seventeen
model-report and eight PTX-proof mutations. The full run took 277.26 seconds
within the unchanged 300-second aggregate limit. Each individual replay retains
its 120-second limit. The [v22 compatibility check](snapshot-v23-v22-compatibility/results.json)
passed two positive replays and all 24 legacy controls in 142.72 seconds. Both
records retain the exact executed reader and control-runner sources, logs and
resource observations outside the frozen snapshot. These checks regenerate
recorded evidence; they perform no fresh Lean checks, model calls or GPU trials.
The [anonymous v23 publication check](snapshot-v23-publication/results.json)
downloaded all eleven files, totaling 50,530,069 bytes, from source `e931a9e`
with TLS verification enabled. Every byte matched the pinned Git commit, and
the downloaded snapshot passed all four positive replays and 49 negative
controls outside Git.
The [actual v23 source CI record](snapshot-v23-source-ci-v1/results.json)
records all twenty jobs passing at source `e931a9e`, including raw six-cohort
regeneration, the frozen ledger controls and the complete proof-test job.
The subsequent publication/CI receipt commit changes only this README and
recorded receipts; source code, Lean libraries, tests, workflow definitions
and every frozen snapshot retain the exact tested source bytes.

The original registry, optimized PTX, original harness and model histories,
closed-model runs, original mutants and H100/MI300X timing cells remain missing.
The following older snapshots and their validation/publication records retain
their original bytes and observations.

The earlier v22 snapshot freezes **3,378 published evidence files** at commit `e7ea523`,
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

The [2026-11-13 bounded artifact refresh](original-artifact-refresh-20261113/results.json) records fresh public repository metadata, release and exact-title/arXiv searches. The inspected KernelCraft repository still reports size zero and no releases; no new author implementation was identified through these endpoints. This does not establish the absence of private or unindexed artifacts and does not alter the frozen ledgers.
