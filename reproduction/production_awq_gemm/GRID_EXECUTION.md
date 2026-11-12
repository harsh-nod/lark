# Complete native grid execution

The `whole-grid-execution-v7` stage proves that the unchanged complete AWQ
program executes every K32 iteration, its guarded converted output stores,
every block and the complete grid. Every launched thread reaches the actual
source halt, and both global input buffers retain their original values.
The original lane/warp/block/grid fuel is sufficient for every supported shape.

This is a theorem about `LarkMFMA.runGrid`; the geometry-guarded `runLaunch`
wrapper is not separately claimed in this stage. A full certificate must
also satisfy the existing `Correct` relation, which requires actual-trace
race freedom and output extraction equal to the specification. Those
obligations remain unfinished. This stage issues zero
AWQ source certificates; the accepted independent production-family count
remains eight.

The preceding [matrix-phase checkpoint](MATRIX_EXECUTION.md) retains its
historical one-K32 scope. Its 17 CI jobs all passed, and the checkpoint was
fast-forwarded to `main`; the [receipt](results/native-matrix-ci-main-v1)
records the checked source commit, publication-only delta and promotion.

## Execution proof

`NativeAwqGemmTailProgram` locates the actual increment, back edge, every
output guard/store and halt in the full 138/226-instruction program.
`NativeAwqGemmKControl` executes the K-counter increment, jump and loop test
with their signed int32 bounds. A nonfinal iteration parks at the existing
reuse barrier; the final iteration falls through to the output guards.

`NativeAwqGemmOutputIndex` proves signed address evaluation and in-bounds
global output locations under the original row guards. It also proves
distinct output coordinates within one lane and distinct writers between
lanes. `NativeAwqGemmOutputStore` executes the original register read,
FP32-to-half conversion and global store, retaining the actual write event.

`NativeAwqGemmOutputRound`, `OutputLoop` and `OutputLane` execute every guarded
output pair. Valid rows take two scalar steps; invalid rows take one and
perform no store. All pairs take at most 64 scalar steps. The final
K-control path consumes three steps, leaving ample room within the original
512-step scalar budget. These proofs preserve registers, setup indices,
epochs, other locations and input buffers, and give the exact per-lane
output write trace. The per-lane stored-value lemma retains `ops.toHalf`.

`NativeAwqGemmTailFold` and `TailBlock` compose the actual 64 lane executions
without overwriting another lane's entry indices or accumulators. They prove
uniform convergence at either the reuse block barrier or the actual halt.
`NativeAwqGemmTileStep` connects staging, both native matrix passes and this
tail using the existing scheduler.

`NativeAwqGemmKLoop` carries the actual accumulator result between K32 tiles.
It proves complete block execution with `2*(K/32)+1` visits: the initial
setup/barrier visit, one staging visit per tile, and one matrix/tail visit per
tile. The last visit executes all output guards and stores before halting.
No arbitrary-operation reassociation is assumed: each new accumulator is
`dot_half1 + (dot_half0 + C)` in the existing source order.

`NativeAwqGemmBlockFrames` proves that complete blocks preserve other blocks'
program counters and global inputs. `NativeAwqGemmGrid` composes every block
in the source grid and proves initialization-to-halt execution, including
the final uniform grid convergence, with grid fuel 1.

## Evidence and limits

The fresh source checker and standalone archive replay check 62 owned Lean
modules, 572 library audits and four 18-audit source bindings: 644 audit
occurrences. The only axioms allowed are `propext`, `Classical.choice` and
`Quot.sound`. All four complete source programs retain their original
instructions, geometry, layout and fuel.

Six altered complete sources fail on false source identity, without a
proof-budget failure. Sixty-two fully rehashed scope controls fail
before archive extraction. These include erased K/output/grid proofs,
changed iteration counts, increased fuel, substituted execution semantics,
invented `runLaunch` acceptance and invented race/reference/certificate claims.

Evidence is under [source checks](results/whole-grid-v1),
[standalone replay](results/whole-grid-replay-v1),
[scope controls](results/whole-grid-scope-guards-v1) and
[wheel resource checks](results/whole-grid-package-v1).
The source-only archive is `results/whole-grid-v1/source-project.tar.gz`
(116,631 bytes, SHA256
`e75e7b1d1a4fddc0044b6ca18f0a6c75ef03f0f774f75558da2a7c3992545330`).
The same bytes are available in the
[complete grid execution release](https://github.com/harsh-nod/lark/releases/tag/native-awq-whole-grid-20261112).
An anonymous download matched the independently replayed archive; all 62
owned model files and 128 source files were bound to commit `1f28d87`, and
all four complete source instances were freshly rerendered. The
[publication receipt](results/whole-grid-publication-v1) records those checks
and the observed CI status. A second cold build on the byte-identical download
is not counted.

The updated reader also replays the preceding matrix-phase archive with its
original [525 audits](results/native-matrix-reader-compatibility-v6) and
[44 scope controls](results/native-matrix-stage-guard-compatibility-v6).
All 60 AWQ Lean resources and the Python reader match the built wheel;
the three native AWQ unit tests also pass.

Every new Lean module and generated source file retains
`maxRecDepth=10000` and `maxHeartbeats=2000000`. Lane fuel remains 512, warp
fuel `tileN/8+1`, block fuel `2*(K/32)+1`, and grid fuel 1. No shape bounds,
native instruction semantics or kernel source changed. This proof stage
makes no GPU launches or model calls.

The paired numerical evidence remains 120 launches across `mi350` and
`mi350-2`, with 820,224 CPU float64 comparisons, zero tolerance failures and
zero host FP16 bit differences. These measurements and the finite symbolic
checks remain separate from the universal proof obligations.

The next steps are final-output coverage and source-order extraction,
actual whole-trace race classification, the dense exact-real bridge and
complete AWQ certificate/CLI support. Original author-adapted PTX, original
model pass rates/token costs and NVIDIA measurements remain separate gaps
in reproducing the paper.
