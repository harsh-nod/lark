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
suite now passes on MI350 CPU, as recorded below. New source CI and anonymous
publication remain release gates. Public main continues to use the validated
v26 ledger until those gates complete.

The [first complete-suite attempt](snapshot-v27-validation-mi350-v1/observer/results.json)
hit the unchanged 300-second aggregate cap at 300.064 seconds after writing
89 of 98 logs. It is a failed run. All logs and the executed helpers are
retained; the [capture inventory](snapshot-v27-validation-mi350-v1/capture.json)
binds all 8,336 files left in the original interrupted workspaces. Those
workspaces, the complete snapshot and original transport archive remain on
MI350. No control or input was removed and the run was not restarted.

The [diagnostic replay](snapshot-v27-replay-profile-v1/results.json) profiled
one complete unchanged snapshot after that failure, performing no Lean, model
or GPU experiment. Its 11.75 seconds include profiler overhead: 7.49 seconds
in the frozen auditor and 2.83 seconds in archive reconstruction. The runtime
revision uses a 1 MiB tar stream buffer while retaining every size, inventory,
fragment and logical-file hash guard. Layout validation runs once inside the
unpacker before any archive is read. All twelve archive-guard tests pass.
The buffer revision's full outcome is recorded below. The frozen v27 snapshot
bytes remain unchanged.

The [second full attempt](snapshot-v27-validation-mi350-v2/observer/results.json)
also hit the same cap, at 300.114 seconds with 91 logs. Its complete logs and
the 58 files left in its interrupted workspaces are retained. The published
source's [actual ledger CI job](snapshot-v27-paper-ci-timeout-v1/analysis.json)
failed with exit code 124 at its 300-second cap after writing 46 logs. That
job is not rerun, and its failure establishes no successful source-CI gate.

The next runtime revision stores temporary control gzip streams at compression
level 0. These remain complete valid gzip/tar files; most large logical members
are themselves compressed proof/history archives. Every member, size bound,
hash, independent replay and control remains required. All ten control-writer
guard tests pass, including mutation isolation, changed part boundaries and
complete regular-file fallback.

The [third full suite](snapshot-v27-validation-mi350-v3/observer/results.json)
passed in **284.218 seconds** on MI350 CPU at source `20f5f77`: all nine
positive replays and 89 negative controls completed under the unchanged limits.
All 89 earlier check records are identical. The [independent return check](snapshot-v27-validation-mi350-v3/independent-return-validation.json)
verifies all 98 retained logs and the four executed helper files against that
exact Git source. The two earlier timeouts remain failures; the new runtime
changes did not alter the frozen snapshot, workload, payload or case roster.
No fresh Lean, model or GPU experiment was performed by these replays.

The fresh source CI run is
[43565831419](https://github.com/harsh-nod/lark/actions/runs/43565831419),
attempt 1 for source `20f5f7760f90c9e0d50e123f2b3a21fe51d40ce6`.
Its [ledger job](snapshot-v27-paper-ci-timeout-v2/analysis.json) reached 86 logs
before hitting the same 300-second cap with exit code 124. All logs and four
executed source files are retained. The job was not rerun; the other jobs in
that workflow are still being observed. Source CI has therefore not passed,
and anonymous full-snapshot publication remains pending. The MI350 pass alone
establishes neither gate. Further runtime work must preserve every byte,
case, hash check and existing limit.

The next [runtime validation](snapshot-v27-runtime-validation-v3/results.json)
records consolidation of duplicate digest passes. One actual physical digest
must match both the outer manifest and archive-layout binding. Every fully
reconstructed logical file is read back and hashed, with its size and exact
file inventory checked before executing the authored frozen auditor. Invalid
structural metadata still triggers the outer archive-integrity check. Sixteen
archive tests include conflicting bindings, post-write corruption, unexpected
files and early malformed layouts; all ten control-writer guards also pass.
The v25 and v26 snapshots replayed outside Git with the initial consolidation,
before adding the early-failure fallback. These checks do not establish a new
complete 98-case or source-CI pass. Both frozen snapshots and v27 remain intact.

The [fourth complete suite](snapshot-v27-validation-mi350-v4/observer/results.json)
then passed all 98 checks in **253.108 seconds** on MI350 CPU at `ceb5eb7`,
with all 89 earlier check records identical. Its returned logs and executed
helpers are independently bound to that exact Git source. The corresponding
[hosted ledger attempt](snapshot-v27-paper-ci-timeout-v3/analysis.json) still
hit the 300-second cap after 66 logs. A CPU-host pass is not a source-CI pass.

The [first complete CI observation](snapshot-v27-source-ci-failed-v1/results.json)
retains 22 successful jobs, the failed ledger job and a `proof-tests` job
cancelled at its unchanged 30-minute job limit. Its raw test log had already
reported an error for the 3,792-path preservation test. The
[isolated ancestry diagnostic](snapshot-v27-ci-scheduling-v1/shallow-results.json)
reproduces why full history is necessary: the same old blob verifies with
complete ancestry and is correctly refused by a shallow view.

The [workflow revision](snapshot-v27-ci-scheduling-v1/final-workflow.yml)
keeps all 24 jobs and all their existing time limits. The four existing numerical
packet audits move to `paper-ledger`; the existing cold fused whole-launch
proof and its report guards move to `fused-real`. Every original named command
remains. `proof-tests` fetches full ancestry with a blob filter and checks the
preservation test before expensive Lean work. No Lean, whole-suite or individual
replay limit increases.

Temporary replay storage uses available `/dev/shm` only when it has at least
4 GiB free and the host has at least 6 GiB available memory; otherwise it keeps
the usual temporary directory. The entire control workspace is constructed
inside the same 300-second window. The [actual storage comparison](snapshot-v27-RAM-storage-equivalence-v1/results.json)
compares every one of **547,956,518 bytes** across all sixteen physical files of
one complete false input on disk and RAM. All 4,135 logical files remain. This
storage check performs no replay or proof and replaces none of the 98 cases.
CI also records timing and I/O diagnostics. These changes still require their
own actual full source-CI result and anonymous publication verification.

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
