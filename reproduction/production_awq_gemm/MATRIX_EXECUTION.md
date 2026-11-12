# Native matrix execution for one K32 iteration

The `native-matrix-phase-v6` stage proves the actual scalar operand loads and
both native K16 matrix passes after the source's middle block barrier. It
executes all 8/16 MFMA instructions for N64/N128, with all four accumulator
results per lane computed from the old register snapshot. The theorem applies
to any valid K32 tile; the surrounding K loop remains unfinished.

Four complete source instances retain their original 138/226 instructions.
Fresh source checks and a standalone replay reproduce 461 library and 64
source audits, over 49 owned modules. Only `propext`, `Classical.choice` and
`Quot.sound` occur. Six altered complete sources fail on false source identity.
Forty-four fully rehashed scope controls fail before extraction, including a
claim that this phase covers all K iterations. No AWQ source certificate is issued.

`NativeAwqGemmMatrixProgram` identifies every A-load, B-load and MFMA site in
the complete unchanged program. Signed-int32 evaluation of every intermediate
fragment address is proved in `NativeAwqGemmFragmentIndex`.
`NativeAwqGemmFragmentValues` carries the dense shared values from the
[proved staging visit](INITIAL_EXECUTION.md) through later register operations.
`NativeAwqGemmFragmentLoad` proves the actual read and assignment, including
the source thread, shared location and ordering epoch in the trace.

`NativeAwqGemmOperandLoop` covers each unrolled four-element group.
`NativeAwqGemmOperandLane` executes eight scalar loads for the first bank of
each pass and four for every later bank. A is loaded once per half; every bank
loads its own B registers. Accumulators and unrelated registers are preserved.
`NativeAwqGemmOperandFold` and `NativeAwqGemmOperandBlock` compose all 64 actual
lane visits and prove convergence at the native matrix site. Later lanes
preserve earlier lanes' operand registers. All lane visits use the original
512 fuel.

`NativeAwqGemmMMAElement` connects the native instruction's lane permutations
to dense A/B coordinates. It proves the sixteen terms and C value read from
the old register snapshot. `NativeAwqGemmMMAValues` computes all 256 results
before any update, proves the actual `runMFMA` result, and identifies every
updated register and participating PC. Memory, the access trace, scalar
indices and ordering epochs are unchanged by the matrix instruction itself.
The existing exact-arithmetic MFMA model is used directly; IEEE accumulation
and rounding equivalence are outside this proof.

`NativeAwqGemmMMABank` composes native operand loading and MFMA execution.
`NativeAwqGemmMMAFold` inducts over all four/eight banks, preserving each
unprocessed accumulator until its own instruction. `NativeAwqGemmMatrixPass`
connects the two K16 passes. `NativeAwqGemmMatrixPhase` proves their complete
execution using the original warp9/17 budget. The source-order result is
`dot_half1 + (dot_half0 + C)` in the existing abstract operations; no
associativity or commutativity is assumed.

`NativeAwqGemmMatrixIteration` connects the actual source staging visit to
these two passes and instantiates that result in every complete source case.
After all native matrix instructions, each lane's PC is `47+14*banks`, at the
K-counter increment. The remaining `runWarp` continuation is retained with
one warp step. The theorem identifies every accumulator and preserves both
input matrices, shared memory, scalar indices and ordering epochs throughout
the matrix phase. It does not execute the increment, back edge or output stores.

Current packets are [source checks](results/native-matrix-v1),
[standalone replay](results/native-matrix-replay-v1),
[scope controls](results/native-matrix-scope-guards-v1) and
[wheel resource checks](results/native-matrix-package-v1).
The source-only archive is `results/native-matrix-v1/source-project.tar.gz`.
The current reader also replays the preceding
[whole-block archive](results/block-staging-reader-compatibility-v5) with its
original 418 audits and [35 controls](results/block-stage-guard-compatibility-v5).

All 47 AWQ Lean resources and the Python reader match the built wheel.
Every new module retains `maxRecDepth=10000` and `maxHeartbeats=2000000`.
Lane/warp/block/grid fuel remains 512, `tileN/8+1`, `2*(K/32)+1`, and 1.
The source kernel, native instruction model, shape bounds and numerical
tolerances are unchanged. This stage makes no model calls or GPU launches.

The K-counter/back-edge execution, full K loop, output stores, whole-launch
termination, actual whole-trace race freedom and dense exact-real reference
equality remain unfinished. The accepted independent production-family count
remains eight. Original adapted PTX, model/token outcomes and NVIDIA
measurements remain separate gaps in reproducing the paper.
