# Six-proof frozen ledger

The v27 snapshot adds the recorded full-size compiled interleaved RoPE
proof to the existing ReLU, GEMV, GEMM, BMM and Linear development proofs.
It preserves all six adapted model cohorts. The original paper remains
incomplete; these abstract scalar proofs establish no IEEE/error bound,
NVIDIA execution, original optimized program or original model outcome.

The [build receipt](snapshot-v27-build-v1/results.json) records creation from
source checkpoint `3d90539b12c1024ace08756b942706d23dff0e5d` in 84.53 seconds.
The snapshot contains 4,133 evidence files plus its auditor and targets,
536,149,253 logical bytes and seven bounded archive parts. Its manifest is
`aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0`.

Every one of v26's 3,792 earlier evidence files retains its original logical
path and SHA256. Both v26 frozen definitions have byte-identical copies under
`frozen-definitions/20261113-v26`. When runtime helpers or documentation have
changed, `preserved_evidence_origins` selects the original ancestor Git blob
for the earlier logical path. The current versions also have separate captures
under `runtime-definitions/20261113-v27`. Concrete source links use the selected
original commit. No old evidence member or development failure was dropped.

RoPE contributes one independent kernel, four retained accepted Main checks,
three rechecks and four direct Lean source-binding refusals. All 17 earlier
development attempts, including 11 failures, remain separate. The reader binds
the actual 24-job source CI, 81-file anonymous publication and guarded non-force
main-promotion records. It reads all 18 archives and 4,414 members as data; it
executes no captured source, object, Lean, model or GPU program.

The full standalone suite requires nine positive replays and 89 negative
controls, totaling 98 checks. All 89 earlier v26 check records must remain
identical. RoPE adds eight coherently rehashed false-claim controls and one
positive replay after them. Limits stay at 120 seconds per replay, 300 seconds
for the complete suite and two independent replay workers. The complete v27
suite, new source CI and anonymous snapshot publication are still pending;
build completion and local CI-ledger assertions do not establish those gates.
Public main continues to use the validated v26 ledger until those gates complete.

```bash
python3 reproduction/paper_results/replay_snapshot.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v27 \
  --source-archive /path/to/2611.02028v1.tar

timeout --kill-after=5s 300s python3 reproduction/paper_results/check_snapshot_controls.py \
  --snapshot reproduction/paper_results/snapshots/20261113-v27 \
  --source-archive /path/to/2611.02028v1.tar --output /tmp/lark-v27-controls
```

Building a new snapshot requires separately staging and committing the source
captures, then using that clean concrete checkpoint:

```bash
python3 reproduction/paper_results/prepare_ptx_rotary_snapshot.py --stage-inputs
# Review and commit the generated captures before the build.
python3 reproduction/paper_results/prepare_ptx_rotary_snapshot.py \
  --evidence-commit FULL_CHECKPOINT_SHA \
  --source-archive /path/to/2611.02028v1.tar \
  --snapshot reproduction/paper_results/snapshots/FRESH_VERSION
```

Existing source captures and snapshots are refused if their bytes differ.
The builder performs no fresh Lean, GPU or model experiment. Standalone replay
uses the complete snapshot, pinned manuscript archive and authored Python
standard-library helpers, outside Git and without the SDK.
