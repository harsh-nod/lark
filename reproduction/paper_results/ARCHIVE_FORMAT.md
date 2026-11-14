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
