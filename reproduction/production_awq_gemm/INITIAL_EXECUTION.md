# Actual block execution through both staging barriers

The `block-staging-v5` development stage checks four complete source instances
against the fixed 138/226-instruction template, then applies universal Lean
execution theorems to each instance. Its standalone archive contains 34 owned
modules. Fresh builds and independent replays reproduce 358 library and 60
source audits, with only `propext`, `Classical.choice` and `Quot.sound`.
Six changed sources fail on their false identity claims, and 35 fully rehashed
scope claims fail before a proof project is extracted. The same reader also
replays the historical first-decode archive and its 90 audits.

`NativeAwqGemmInitial` proves execution of all thirteen index assignments,
sixteen/thirty-two accumulator writes, K-counter initialization and the initial
loop branch. All 31/47 instructions use the unchanged lane512 budget. The
resulting state has the exact indices, zero accumulators and first-barrier PC;
memory, the actual trace and ordering epochs are unchanged.

`NativeAwqGemmInitialBlock` folds that execution in the actual 64-lane source
scheduler. It proves convergence of the one native wave64 and rewrites the
first `runBlock` visit to its continuation after the block-barrier resume.
The continuation retains the remaining original instruction stream and fuel.

`NativeAwqGemmAStage` proves the row guard, both eight-trip A-staging loops and
their join into B staging. A valid row consumes 36 scalar instructions and
records eight input-read/shared-write pairs in source order.
A padded row consumes 35 instructions, performs no global load and records
eight typed half-zero shared writes. Every signed intermediate index and
global/shared bound is checked by the existing machine.

`NativeAwqGemmAValues` proves every staged cell's value and that all memory
outside those eight cells is preserved. It also proves coverage of the local
16×32 A tile and a shared-cell inverse that recovers the unique writing thread.
The phase preserves both input matrices, all accumulators and ordering epochs.

`NativeAwqGemmBStage` proves every B-staging chunk, including its signed row
and column assignments, all eight read/write iterations, failed loop tests,
counter increments and back edges. The four/eight chunks consume 158/314
scalar instructions and record 64/128 actual memory events.
`NativeAwqGemmBValues` proves all staged B values, the outside-memory frame,
and a shared-cell inverse recovering its global writer, chunk and element.

`NativeAwqGemmStaging` composes the actual A-then-B order of a single lane.
It reaches the middle barrier using the unchanged lane512 fuel. The exact
scalar counts are 193/194 for N64 and 349/350 for N128, depending on the A-row
guard. Both shared value families survive, both input matrices are preserved,
and the accumulators and ordering epochs are unchanged. The four complete
source instances each instantiate this theorem, including the output state,
pointwise values, outside-memory frame and exact trace length.
`NativeAwqGemmStagingFrame` proves that executing a lane preserves all other
lanes' PCs and scalar indices. `NativeAwqGemmStagingFold` identifies the actual
64-lane monadic scheduler with the combined per-lane state transformers, in
source order. Every lane reaches the middle block barrier.
`NativeAwqGemmStagingBlock` proves convergence of the native wave64, resumes
that barrier and rewrites the current `runBlock` visit to its remaining
continuation. It also composes the first two block visits, from the source's
initial PC0 through the second barrier in the first K32 chunk.

`NativeAwqGemmStagingMemory` uses the shared writer inverses to preserve
earlier lanes' cells during later lanes' execution. It proves all lanes' A/B
values, both input matrices and memory outside the block's staged cells remain
as specified. The accumulators are unchanged; epochs are exactly the existing
machine's block-barrier update.
`NativeAwqGemmStagingTiles` covers every dense shared cell: the 16×32 A tile
with correct row-tail zero padding and the 32×tileN B tile. Their values match
the independent dense global input coordinates. It also identifies every
native fragment's shared value. Executing the scalar fragment loads and the
MFMA instructions remains future work.

Current packets are [source checks](results/block-staging-v1),
[standalone replay](results/block-staging-replay-v1),
[scope guards](results/block-staging-scope-guards-v1) and
[wheel resource checks](results/block-staging-package-v1).
The source-only archive is `results/block-staging-v1/source-project.tar.gz`.

The earlier `lane-staging-v4` archive remains available in the
[per-lane staging release](https://github.com/harsh-nod/lark/releases/tag/native-awq-lane-staging-20261112).
An anonymous download matched the independently replayed archive; all 29
owned model files and 95 source files were bound to commit `c961103`, and the
four complete source instances were freshly rerendered. The
[receipt](results/lane-staging-publication-v1) records those checks and the
CI status at publication. It does not count an additional cold build on the
identical download. The current reader also freshly replays the historical
[first-decode](results/first-decode-reader-compatibility-v3) and
[A-staging](results/a-staging-reader-compatibility-v3) archives, retaining
their respective 90- and 256-audit scopes.

The earlier `a-staging-v3` archive remains available in the
[public A-staging release](https://github.com/harsh-nod/lark/releases/tag/native-awq-a-staging-20261112).
An anonymous download matched the independently replayed bytes, all twenty
owned model files matched source commit `2f505a7`, and all four source instances
were freshly rerendered from that commit. This check did not repeat the cold
build on the identical download. Its [receipt](results/a-staging-publication-v1)
binds 86 source files and records the CI status at publication.

Every new module retains `maxRecDepth=10000` and `maxHeartbeats=2000000`.
Lane/warp/block/grid fuel remains 512, `tile_N/8+1`, `2*(K/32)+1`, and 1.
No source kernel, shape contract, numerical tolerance or machine limit changed.
Explicit state arguments and proved frame properties avoid repeated expansion
of the functional loop states during composition.

Scalar matrix loads, MFMA execution, the complete K loop, final output stores,
whole-trace race freedom and dense-reference equality remain unfinished.
This stage issues **zero AWQ source certificates** and does not increase the
eight accepted independent production-family count. It adds no model calls or
GPU launches to the earlier paired numerical study.
