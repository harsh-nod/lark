# Audit of every paper table and figure

[Result-by-result ledger](results/RESULTS.md) · [machine-readable audit](results/audit.json)

The original paper is **not fully reproduced**. This audit inventories all 17
tables and seven outer figure groups in the arXiv v1 preprint, plus 16 narrative
anchors for results and implementation requirements that a table-only checklist
would miss. Configuration tables and method diagrams are identified separately
from measurements. Overlapping items do not define a completion percentage.

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
