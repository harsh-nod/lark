# Coverage snapshot after the wave-reduction study

[Result-by-result ledger](results/RESULTS.md) · [machine-readable audit](results/audit.json)

This snapshot maps every paper table, outer figure group and additional result
anchor to evidence at experiment-code commit
`35a6383ba569197a44c5cd0d23a03c215ec1f6f2`. It includes the later independently
adapted production SiLU, canonical-real algebra and full-wave reduction studies.
It also freezes the recorded public-release searches and successful CI response
for that commit. **The original paper is not fully reproduced.** Original
experiment/history rows remain unverified; overlapping items are not a
denominator for a completion percentage.

The selected study summaries, validation records and documentation are copied
from their pinned Git blobs into `evidence.tar.gz`, with a per-file manifest and
provenance map. Newly recorded GitHub responses have separate origins in that
map. The trusted repository-authored `auditor.py` and authored `targets.json`
are frozen in the same archive. The manuscript is read as data and is never
executed. This audit checks source coverage and integrity, and does not prove
the validity of an experiment by hashing its report. Each linked study retains
its own proofs, raw evidence and validation scope.

Replaying needs Python's standard library, this snapshot and the original
arXiv v1 source archive with SHA-256
`095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2`:

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --source-archive /path/to/2611.02028v1.tar
```

The checker extracts only regular safe-path files into a fresh temporary
directory, checks the exact frozen file set, and runs the frozen auditor to
regenerate and compare the ledger. It needs no historical checkout, Git
history, GPU, Mathlib or model endpoint. Existing-study links point to exact
GitHub blobs at the experiment commit; the release/CI records are local to this
snapshot. Future changes to repository documentation do not affect replay.

`--build` creates fresh outputs from definitions and pinned Git blobs; it
requires repository history and refuses existing generated outputs. The default
mode only checks the published snapshot. The older
[historical audit](../../README.md) remains available with its original inputs.

The remaining dependencies are explicit: original kernels/adaptations/mutants,
agent harness and traces, closed-model regeneration incompatible with free
offline calls, original NVIDIA measurements, and historical development
records. Broader packed/vector, multiwarp, tiled and online/combined kernel
proofs remain software work. Neither these dependencies nor finite AMD tests
are relabeled as completed original results.
