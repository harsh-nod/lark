# Frozen evidence storage

The default remains the immutable v25 snapshot. Version 1 snapshots retain
their original single `evidence.tar.gz`, provenance binding and replay path.

Version 2 is an opt-in storage format for the larger evidence ledger. Its
`evidence-layout.json` binds each physical archive, every contained fragment
and each complete logical evidence file by byte count and SHA256. Logical
files retain their original bytes and paths. Large files are split into
contiguous storage chunks; their full bytes are reassembled before the frozen
auditor reads them. Code and compiled objects inside evidence remain data.

The existing 10,000,000-byte limit per tar entry remains unchanged. Each new
physical archive is bounded at 90,000,000 bytes; the writer partitions at
85,000,000 bytes of tar entries to leave room for headers and compression
overhead. These storage bounds change no proof, workload, launch, fuel,
replay, aggregate-time or worker limit, and remove no evidence or control.

Version 2 rejects missing, duplicate, reordered, non-contiguous, oversized and
unsafe fragments. It verifies each archive before extraction, each fragment
while reading, and each complete logical digest after assembly. The logical
roster and hashes must match the independent evidence manifest. The authored
frozen auditor and targets must still match their separately bound definitions.

Twelve focused tests cover a real 10,000,001-byte logical payload, multiple
parts, deterministic encoding, preserved empty/code files, coherent chunk-hash
forgery, manifest forgery, path/directory collisions, typed metadata, existing
output preservation, builder integration, concatenated gzip control streams
and the unchanged legacy entry guard. The version 2 streaming reader uses
`gzip.GzipFile` to decode every concatenated gzip member before reading the
complete tar stream, with the same fragment and logical-file checks.
The [full real-corpus compatibility record](snapshot-v26-format-compatibility-v1/results.json)
checks all 3,625 frozen v25 files, including all 3,623 original evidence members.
Legacy replay passed in 7.3327 seconds and version 2 replay in 7.6966 seconds;
encoding and both sequential replays took 24.4268 seconds in total. All logical
bytes and hashes and every original v25 snapshot byte remain identical. The
two new archive parts are 34,995,694 and 48,598,737 bytes. Raw prototype copies
remain retained locally; this receipt contains the original commands, logs,
source identity and complete-corpus bindings. This verifies storage compatibility,
not BMM/Linear ledger integration or a completed v26 snapshot.

After adding concatenated-gzip support, the
[updated-reader compatibility record](snapshot-v26-stream-compatibility-v1/results.json)
replays the same retained version 2 prototype with all 3,625 logical files in
8.2407 seconds. It preserves every prototype and original v25 snapshot byte;
it does not regenerate the prototype or repeat the earlier legacy replay.
All 12 version 2 storage tests and all three existing legacy control-archive
tests passed together in 0.371 seconds.

Standalone version 2 replay requires the trusted sibling
`snapshot_archives.py`. Version 1 replay does not import that helper. The
existing 120-second auditor cap and 300-second full control-suite cap, with
at most two independent replay workers, remain required. No captured code,
Lean proof, GPU trial or model call is run by this storage layer.

`snapshot_control_archives.py` extends the copied false-control archives to
version 2. It preserves every complete logical byte while reusing immutable
compressed fragments; each worker owns its changed metadata, output parts and
replay. Opaque fragment names depend on logical file names, so adding a control
does not invalidate unchanged compression. Unsafe logical paths are deliberately
retained as control data for the actual trusted replayer to reject. They are
never used as physical archive paths by the writer.

The control runner binds the new layout and complete logical manifest in
provenance, supplies the trusted version 2 reader helper outside Git and keeps
all earlier controls. When both new proof groups are declared, it adds eight
BMM and eight Linear semantic controls and a positive replay after each group.
The complete v26 snapshot and its full control-suite run remain pending.

Eight control-writer tests, twelve storage tests and the three existing legacy
control-archive tests passed together in 0.816 seconds. They cover complete
multi-part reconstruction, the actual 10,000,001-byte boundary, empty/code/long
logical paths, retained unsafe control bytes, two independent workers,
deterministic compression reuse, old copied-part cleanup without dropping a
logical byte, corrupt-baseline refusal and complete provenance rehashing.

The [complete real-corpus control-writer validation](snapshot-v26-control-storage-validation-v1/results.json)
then exercised all 3,625 frozen v25 files through the new writer and trusted
standalone replayer. The positive replay passed; a completely rehashed GEMM
kernel-count overclaim failed at its semantic gate, and an additional retained
unsafe logical member failed at the trusted path gate. Cache construction,
three full copied control archives and all three sequential replays took
25.0956 seconds. Every original logical file remains present; only the two
selected GEMM metadata files change in that false control. Both the original
v25 snapshot and the retained schema-two prototype remain byte-identical.
The complete raw control snapshots remain retained locally. This checks the
new control-storage path, not the final v26 snapshot or its full control suite.

The public downloader now derives its complete file roster from the pinned Git
commit, so deletion or replacement in the local working tree cannot omit a
published archive part. Version 2 includes both trusted archive helpers in
addition to the replayer and control runner; version 1 retains its original
two-helper roster. Six offline roster tests passed in 0.594 seconds, including
the real unchanged v25 eleven-file download roster, missing-part refusal and
the expected v26 eight-positive/eighty-one-negative counts. A v26 anonymous
download and full control-suite pass have not yet been recorded.

`prepare_ptx_extended_snapshot.py` assembles the next ledger from the immutable
v25 definitions only after both complete BMM/Linear publication, source CI,
main-promotion and validation receipts exist. Its preflight checks all 3,623
earlier evidence paths and hashes, both byte-identical historical definitions,
all five PTX proof packets and the complete six-cohort comparison. The old
definitions live at committed `frozen-definitions/20261113-v25/` paths, so their
source links exist at the evidence checkpoint. No uncommitted local-evidence
path is used. Only the exact v25 auditor source can be augmented.

The new frozen auditor adds separate BMM/Linear checks and renders five
independent development kernels with the official rechecks, failed exports and
partial development attempts distinguished. It keeps every paper experiment/
history reproduction flag false and supplies no completion percentage. Five
preparation/renderer tests passed in 0.592 seconds. The actual v26 build and
full control suite remain separately required.

The [first v26 build record](snapshot-v26-build-v1/results.json) assembled the
candidate snapshot in 68.4448 seconds from source `784634ae3902539280c28e2ca2803a46d8fc918a`.
It contains 3,792 evidence files, or 3,794 logical files including its new
auditor and targets, totaling 281,252,397 logical bytes. The four archive parts
are 34,543,398, 80,333,995, 83,660,563 and 32,837,752 bytes. All earlier 3,623
evidence paths and hashes and both historical definitions are retained. The
original v25 snapshot is byte-identical. This build creates no fresh proof,
model or GPU result and does not satisfy the pending full control-suite,
anonymous publication, new source CI or main-promotion gates.
