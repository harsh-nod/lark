# Native llm.c softmax source study

This independent AMD adaptation retains all three passes of llm.c
`softmax_forward_kernel7`: maximum, exponentiation/sum and normalization. It
implements both the clamped-read original and the guarded-read repair described
in [Appendix A.14 of the paper](https://arxiv.org/html/2611.02028v1#A1.SS14).
The complete sources are bound to their translated programs. Instruction-level
Lean witnesses and complete finite address traces expose the original conflict;
finite numerical tests pass on both AMD hosts. Conflict-state reachability,
universal repaired-launch correctness and its reference bridge remain open.
**This development profile issues zero source certificates.**

## Source and supported launch

[Provenance](provenance.json) pins
[llm.c commit f1e2ace](https://github.com/karpathy/llm.c/blob/f1e2ace651495b74ae22d45d1723443fd00ecd3a/dev/cuda/softmax_forward.cu).
The upstream source, `common.h` and MIT license are retained in [upstream/](upstream/).
The Git blob's raw SHA256 is
`5bc29aae3b655fbccdb40a9dc3a071e64f9b9f53e2c98d0fb0c82e346990013e`.
The earlier race-excerpt study recorded a full-source hash after adding one
trailing newline; the new provenance records both representations explicitly.
This pin identifies independently selected public source, not the authors'
unreleased adapted kernel or exact experiment revision.

The closed launch has FP16 contiguous, mutually disjoint input/output buffers
of shape `[rows,50257]`, 1,024 threads per block and one block per row. Physical
wave64 contains two complete logical32 groups. Positive row counts must satisfy
`rows * 50257 < 2^31`, so the maximum is 42,730 and the upstream default of
8,192 rows is included. The signed bound applies to addresses actually computed
after the source's clamp or bounds guard.

[Rewrites](rewrites.json) distinguish scalarization/translation from semantic
departures. Input and output storage are changed from upstream FP32 to FP16,
as in the paper's stated adaptation. The source keeps unrounded FP32 sums,
FP16 exponentials in output, both separate eight-element private arrays and all
four block barriers. The maximum reduction uses logical32 **down** shuffles;
the sum uses logical32 **XOR** shuffles. The repair bounds the normalization
load and removes its clamp; the two separate load/store loops remain.

The opt-in [reader](../../lark_kernels/native_softmax.py) handles this closed
source family with unchanged machine definitions and fuel `(4096,8,5,1)`.
It gives each private-array cell its actual thread owner. A dedicated reserved
`-INFINITY` spelling maps to the reserved, executable
`Ops.literal(-1,4294967296)` key; `withSeed` supplies its abstract value. Lean
checks that this expression evaluates to the supplied seed. No ordinary
rational, real or IEEE interpretation of that key is asserted. Ordinary task parsing and
registered certificate profiles are unchanged. The secondary 32-thread witness
described by the paper is outside this 1,024-thread study.

## Checked proof scope

The latest [component packet](results/components-v3/results.json) freshly builds
eight Lean modules, audits 52 declarations and rejects ten false claims.
Its [archive replay](results/components-validation-v3/results.json) repeats the
reader check, build and refusals with Git unavailable and no own compiled Lean
cache. It also reproduces the full finite traces from frozen source. Earlier
`components-v1` packets retain their original narrower row bound. Both earlier
component versions are superseded by the executable-seed correction below.

[All four CI jobs](https://github.com/harsh-nod/lark/actions/runs/42998373043)
passed at corrected source commit `8ad3fdadb0605ddfbf85e9eb57ce674b3f3024f3`.
The dedicated source job repeats the fresh component/finite-trace archive
checks and four contract tests. The other jobs recheck the existing general
proof/test suite and real-certified profiles. The
[saved API responses and raw logs](results/source-ci-v1/results.json) identify
the exact component source commit. Subsequent numerical/publication receipts
change metadata only. This component CI run does not validate the later
maximum-prefix extension.

The four local proof files establish:

- Exact full-program/interface binding: 117 original instructions and 116 repaired
  instructions, with the pinned source, layout, geometry and fuel.
- Column coverage, ownership, address bounds and injectivity.
- A sufficient access classification that implies race freedom.
- Actual single-instruction reader/writer traces from explicit intermediate
  states, their conflicting pair and the repaired guard's skipped load.

The Lean instruction witnesses use arbitrary arithmetic operations and values.
They do **not** prove that the initializer reaches those intermediate states.
Likewise, the sufficient classification theorem does not prove that every access
in every complete repaired launch satisfies the classification. Those are
separate remaining source-execution obligations. There is no canonical-real
softmax theorem, IEEE equivalence theorem or numerical error bound here.

The later [actual maximum-prefix proof](../../lean/Lark/NativeSoftmaxMaxPrefix.lean)
starts at the actual machine initializer for both complete source variants. Every
valid thread, for every supported row count and arbitrary arithmetic operations,
inputs and outside memory, executes all seven outer iterations, all eight
components per iteration, every clamp branch and both false loop exits. With
the unchanged lane fuel 4,096, it parks at PC20 immediately before the first
logical32 shuffle. Register0 contains the exact source-ordered maximum fold,
including every clamped duplicate read and explicit input half conversion.

The actual prefix has exactly 56 accesses. All are reads of input buffer1; all
memory and epochs remain unchanged, and prefix race freedom is derived without
assuming it. The [exact count theorem](../../lean/Lark/NativeSoftmaxMaxPrefixCost.lean)
establishes 497 scalar IR instructions for tid0..80 and 498 for tid81..1023.
These are model instruction counts, not GPU instructions or NVIDIA timings.
Noncommutative word-valued witnesses check the source operand/cast order at both
sides of the final-clamp boundary.

The [maximum-prefix packet](results/max-prefix-v1/results.json) and its
[independent archive replay](results/max-prefix-validation-v1/results.json)
freshly build 20 local Lean modules, audit 143 declarations and reject 18 false
claims. They retain the exact source/reader/IR/interface binding and complete
proof closure. The replay starts without Git or cached own
Lean objects and also compares both complete finite address traces. That prefix
packet leaves the logical
reductions, shared partial stores, barriers, exponentiation/sum and normalization
passes, whole block/grid execution, conflict-state reachability and reference
bridge remain open. This stage still issues zero source certificates.
Six [fully rehashed stage controls](results/max-prefix-stage-guards-v1/results.json)
separately reject invented certificates/whole-launch/reference claims, an
omitted input-trace audit and earlier components relabeled as this prefix.
All six fail before extraction or compilation.
The [wheel audit](results/max-prefix-packaging-v1/results.json) checks that the
complete 20-module proof closure and closed reader are packaged byte-for-byte.

[All four maximum-prefix CI jobs](https://github.com/harsh-nod/lark/actions/runs/43007162456)
passed at source commit `b02f85d3e3f825fb0b2d8ca0782061fddc7bb75e`.
The [saved API responses and raw logs](results/max-prefix-ci-v1/results.json)
record the fresh prefix check, archive replay and six stage refusals, plus the
existing real-profile checks and general suite: 169 tests run, 160 passed and
nine optional skips. All 74 selected proof, reader, checker, runtime, test,
packaging and workflow files match that source commit byte-for-byte. This run
does not validate later lane-fold or wave extensions.

The later [actual maximum first-wave proof](../../lean/Lark/NativeSoftmaxMaxFirstWave.lean)
executes both complete source variants from the actual initializer through the
unchanged physical wave64 scheduler. All 64 lanes complete their scalar prefixes,
then execute the five logical32 downward shuffles and maximum updates at distances
16, 8, 4, 2 and 1. The two logical leader lanes store their exact reduction trees
in distinct shared bank0 slots `2*warp` and `2*warp+1`. Every lane parks at PC32,
the first block barrier, using the unchanged lane/warp fuel 4,096/8. The theorem
covers every valid row and native wave for every supported shape, with arbitrary
operations, inputs and outside memory.

The [source-ordered tree witnesses](../../lean/Lark/NativeSoftmaxMaxWaveTree.lean)
retain the bit-reversed leader leaf order and every overflowing lane's self update,
without assuming associativity, commutativity or idempotence of maximum.
The [exact access count](../../lean/Lark/NativeSoftmaxMaxWaveCount.lean) is 3,586
records: 3,584 input reads and two shared writes. Global memory, the other shared
bank and all synchronization epochs are preserved. Actual-trace
classification derives first-wave race freedom without assuming it. The barrier
has not resumed; shuffles do not acquire a memory fence.

The [first-wave source packet](results/max-first-wave-v1/results.json) and
[independent archive replay](results/max-first-wave-validation-v1/results.json)
freshly build 33 local Lean modules, audit 287 declarations and reject 33 false
claims. The replay starts without Git or cached own Lean objects and again
compares both complete finite address traces. Nine
[fully rehashed stage controls](results/max-first-wave-stage-guards-v1/results.json)
reject stronger claims, missing principal audits/refusals, changed fuel/counts
and earlier prefix evidence relabeled as a wave, all before extraction. The
[wheel audit](results/max-first-wave-packaging-v1/results.json) checks the complete
33-module closure and closed reader byte-for-byte.

[All four first-wave CI jobs](https://github.com/harsh-nod/lark/actions/runs/43014089106)
passed at source commit `e899c9d867b322b155610587b3e0b28676d57e25`.
The [saved API responses and raw logs](results/max-first-wave-ci-v1/results.json)
record the fresh source/archive checks and nine stage refusals, the existing
real-profile checks, and the general suite: 169 tests run, 160 passed and nine
optional skips. All 93 selected implementation files match that source commit
byte-for-byte. This run does not validate the later first-block extension.

The later [first-block proof](../../lean/Lark/NativeSoftmaxMaxFirstBlock.lean)
composes all sixteen physical waves through the scheduler's actual sequential
wave-fold. Every participating thread starts at the actual initializer and
reaches PC32. All thirty-two source-ordered partial maxima survive later waves;
the proof preserves their distinct shared slots and the controls of waves that
have yet to execute. It covers both complete source variants and every valid
row for every supported shape, with arbitrary operations, inputs and outside
memory.

The [first barrier proof](../../lean/Lark/NativeSoftmaxMaxBarrier.lean) resumes
that actual block barrier, advancing all 1,024 participating PCs to 33 and their
block epochs to 1. Memory and the historical trace stay unchanged. The full
`runBlock` call decomposes into the same scheduler with four remaining block
phases and that resumed state. The proof leaves those remaining phases explicit.
The exact phase trace has 57,376 accesses: 57,344 input reads and thirty-two
shared partial writes. Actual-trace classification derives phase race freedom.

The [block source packet](results/max-first-block-v1/results.json) and
[independent archive replay](results/max-first-block-validation-v1/results.json)
freshly build 37 local Lean modules, audit 357 declarations and reject 41 false
claims. They retain the full source/reader/IR/interface binding; the replay uses
no Git or own compiled cache and compares both complete finite address traces.
A separate witness interprets the maximum operation as `3*a+b` and checks the
actual fold's final partial in logical slot 31 against its exact integer value.
Ten [fully rehashed stage controls](results/max-first-block-stage-guards-v1/results.json)
reject invented claims, changed counts/fuel, omitted principal audits/refusals
and earlier wave evidence relabeled as a block, before extraction.
The [wheel audit](results/max-first-block-packaging-v1/results.json) checks the
complete 37-module closure and closed reader byte-for-byte.

[All five first-block CI jobs](https://github.com/harsh-nod/lark/actions/runs/43018861366)
passed at source commit `85a2298ffc397eea8082ddb6b5a43f5ef421e7a5`.
The [saved API responses and raw logs](results/max-first-block-ci-v1/results.json)
retain the source/archive checks, ten stage refusals, existing real-profile
checks and general suite: 169 tests run, 160 passed and nine optional skips.
All 103 selected source files match that commit byte-for-byte. This run does
not validate the later serial-maximum extension.

The later [complete maximum-pass proof](../../lean/Lark/NativeSoftmaxMaximum.lean)
executes the thread-zero serial reduction of all thirty-two partials and resumes
the actual second block barrier. It uses the scheduler's sequential lane and
wave folds: the leader needs the old partials while pending, and later skip lanes
preserve the stored result. All 1,024 participating threads now reach PC43 with
block epoch2, with the exact source-ordered row maximum in shared slot0. Both
source variants, all supported rows and arbitrary operations/inputs are covered.
The original scheduler retains three block phases after this point; the machine
fuel is unchanged. The exact 57,409-access trace includes 57,344 input reads,
32 shared reads and 33 shared writes. Its classification derives phase race freedom.

The [maximum-pass source packet](results/maximum-v1/results.json) and
[independent replay](results/maximum-validation-v1/results.json) freeze the full
source binding, freshly build 47 Lean modules, audit 512 declarations and reject
52 false Lean claims. The replay starts without Git or any own
compiled cache and compares both complete finite address traces. An integer
witness interprets the maximum operation as `3*a+b`, checks all thirty-two
partials, and checks the serial fold's actual shared result. This detects changes
to reduction order without assuming commutativity, associativity or idempotence.
Fifteen [stage controls](results/maximum-stage-guards-v1/results.json) reject fully
rehashed false claims before extraction, including earlier first-block evidence
relabeled as a complete maximum pass. The [wheel audit](results/maximum-packaging-v1/results.json)
checks all 47 proof modules and the reader byte-for-byte.

[All five maximum-pass CI jobs](https://github.com/harsh-nod/lark/actions/runs/43026870118)
passed at source commit `1979f20db03d4fa57d78c8274c978e7cbd54cb58`.
The [saved API responses and raw logs](results/maximum-ci-v1/results.json)
record the fresh source/archive checks and fifteen stage refusals, the existing
real-profile checks, and 169 general tests: 160 passed and nine optional skips.
All 88 selected implementation, proof and fixture files match that source commit
byte-for-byte. Later tracked changes contain only study documentation and evidence.

The later [scalar exponentiation/sum prefix](../../lean/Lark/NativeSoftmaxExpPrefix.lean)
starts after the proved maximum pass. Each selected lane executes all seven
outer rounds: eight clamped input loads into private storage before that round's
exponential stores. Valid columns store converted outputs and add the unrounded
exponential to the source-ordered sum; invalid columns skip the private read,
output write and sum update. Earlier outputs survive subsequent iterations.
The false outer exit initializes the shuffle temporary and parks at PC70,
before the first logical32 XOR sum shuffle. This is an individual-lane execution
family for both complete sources, all supported shapes/rows and arbitrary
operations, inputs and outside memory.

The [exact count proof](../../lean/Lark/NativeSoftmaxExpPrefixCounts.lean) gives
982 scalar instructions, 213 added accesses and 50 valid stores for tids0..80;
tids81..1023 use 978 instructions, 211 accesses and 49 valid stores. The original
lane fuel stays4,096. Block epoch2 and the native indices survive. Actual prefix
trace classification derives race freedom. The output proof retains both half
conversions, and the sum proof retains the unrounded exponential and operand order.

The [source packet](results/exp-prefix-v1/results.json) and
[independent replay](results/exp-prefix-validation-v1/results.json) freshly build
62 Lean modules, audit733 declarations and reject72 false Lean claims. The
complete source/reader/IR/interface binding and constructive maximum-pass folds
remain included. Four integer witnesses at tids0,80,81,1023 check both the actual
run's sum register and an actual converted output against independently computed
values. Their operations distinguish subtraction order, accumulation order and
input/output conversion. The replay starts without Git or own compiled cache
and compares both complete finite address traces. Twenty-four
[rehashed metadata controls](results/exp-prefix-stage-guards-v1/results.json)
reject false certificates, collective/whole-kernel claims, changed counts/values,
missing principal proofs and earlier maximum-pass evidence relabeled as this
prefix, before extraction. The [wheel audit](results/exp-prefix-packaging-v1/results.json)
checks all62 required proof modules and the closed reader byte-for-byte.

All five jobs in [CI run43039634652](https://github.com/harsh-nod/lark/actions/runs/43039634652)
passed at source commit `1cfcf67d970d69ee9bdd2699c704171f944c5f18`.
The [saved CI packet](results/exp-prefix-ci-v1/results.json) retains the raw
logs and job metadata, including the fresh export/replay and24 rehashed metadata
refusals. The general suite ran169 tests:160 passed and9 optional tests skipped.
All106 selected live implementation, proof, fixture and workflow files match
the checked commit byte-for-byte; later changes contain only this study's
documentation and frozen evidence. This CI run covers the scalar lane prefix
through PC70 and the retained maximum phase.

The scalar-prefix packet leaves collective sum execution, serial sum,
normalization, whole-grid composition, conflict-state reachability and the
canonical-real reference bridge open. It issues zero source certificates and
does not reproduce the paper's original NVIDIA or historical model results.

The later [complete native64 wave proof](../../lean/Lark/NativeSoftmaxExpWave.lean)
starts at the proved maximum state and executes all seven scalar rounds, five
logical32 XOR/add stages and two distinct shared-bank1 partial stores. Every
lane parks at PC82, at the third block barrier, with block epoch2. The theorem
uses the original lane/warp fuel and applies to both bound sources, every
supported row/shape and arbitrary operations, inputs and outside memory. It
also supports a cohort entry that preserves the preconditions needed by later
waves. The addition tree follows source order and snapshot transport; neither
associativity nor commutativity is assumed. Its actual wave trace is proved
race-free.

The [source packet](results/exp-wave-v1/results.json) and
[independent replay](results/exp-wave-validation-v1/results.json) freshly build
73 Lean modules, audit 870 declarations and reject 88 false
Lean claims. The replay starts without Git or an own compiled cache and
compares both complete finite address traces. Six integer witnesses check the
actual run's stored partials in both logical groups of warps0,1,15. The model
uses noncommuting addition and distinct half-conversion, subtraction and
exponential operations. Its separate CPU calculation distinguishes reversed
addition, sequential snapshot updates, cross-half peers and the tid80/81 tail
boundary. The 34 [rehashed report controls](results/exp-wave-stage-guards-v1/results.json)
reject invented stronger claims, wrong endpoints/partition values, missing
principal proofs and earlier scalar-prefix evidence relabeled as a complete
wave. The [wheel audit](results/exp-wave-packaging-v1/results.json) matches all
73 required proof modules and the reader byte-for-byte.

All five jobs in [CI run43046411154](https://github.com/harsh-nod/lark/actions/runs/43046411154)
passed at source commit `8ce41605022ec2b8bf4ac9db18b166c155e130d7`.
The [saved CI packet](results/exp-wave-ci-v1/results.json) preserves the raw logs
and job metadata, including fresh export/replay and all34 rehashed metadata
refusals. The general suite ran169 tests:160 passed and9 optional tests skipped.
All120 selected live implementation, proof, fixture and workflow files match
the checked commit byte-for-byte. Later changes contain only this study's
documentation and frozen evidence. The run covers the complete native64 wave
through PC82 together with the retained scalar prefix and maximum pass.

The wave packet stops before the third barrier resumes and leaves the
complete16-wave block phase and serial sum to the later reduction-prefix
milestone below. It issues zero source certificates and does not reproduce
the original NVIDIA timings or historical model experiments.

The later [constructive four-phase reduction prefix](../../lean/Lark/NativeSoftmaxReductionPrefix.lean)
executes all 16 exponentiation/XOR-sum waves, stores all 32 logical partials,
resumes the third barrier, and executes thread0's source-ordered serial sum.
The fourth barrier then resumes all 1,024 threads at PC93 with block epoch4,
the exact row sum in shared bank1/slot0, and all 50,257 converted exponential
output values preserved. The actual four-phase prefix returns `Some` from
the source initializer. A continuation theorem links that prefix to the
unchanged `runBlock`, leaving one original block phase for normalization.
Both full bound sources, all supported shapes/rows and arbitrary operations,
inputs and outside memory are covered. No sum associativity or commutativity
is assumed. The exact prefix trace has273,700 accesses and its classification
derives race freedom.

The [source packet](results/reduction-prefix-v1/results.json) and
[independent replay](results/reduction-prefix-validation-v1/results.json)
freshly build 90 Lean modules, audit 1,083 declarations and reject 103 false Lean
claims. The replay starts without Git or an own compiled cache and compares
both complete finite address traces. A full-prefix integer model checks the
actual row total and preserved first/last output values. A separate
noncommuting `7*a+b` checksum checks the actual serial phase from a synthetic
PC83/epoch3 entry with partial slots 1..32; that checksum is not a full-prefix
witness. The six earlier noncommuting wave witnesses remain included.
The 52 [fully rehashed metadata controls](results/reduction-prefix-stage-guards-v1/results.json)
reject stronger stage claims, wrong counts/fuel, missing principal proofs,
incorrect diagnostic scope and earlier wave evidence relabeled as this
prefix before extraction. The [wheel audit](results/reduction-prefix-packaging-v1/results.json)
matches all 90 required proof modules and the closed reader byte-for-byte.

All five jobs in [CI run43057612879](https://github.com/harsh-nod/lark/actions/runs/43057612879)
passed at source commit `b8bada94ed2d1e555ca47d39ab3fc1904f7f7cda`.
The [saved CI packet](results/reduction-prefix-ci-v1/results.json) retains raw
logs and job metadata, including fresh export/replay and all 52 rehashed
metadata refusals. The general suite ran 169 tests: 160 passed and nine optional
tests skipped. All 141 selected live implementation, proof, fixture and workflow
files match the checked commit byte-for-byte. Later tracked changes contain
only this study's documentation and frozen evidence. The run validates the
constructive four-phase prefix through PC93/epoch4 and its preserved outputs.

Normalization execution, whole-grid composition, conflict-state reachability
and the canonical-real/IEEE reference bridges remain open in this packet.
It issues zero source certificates and does not reproduce the paper's original
NVIDIA timings or historical model experiments.

A bounded [artifact recheck](results/exp-wave-artifact-recheck-v1/results.json)
at 2026-11-11 15:06:50 UTC found no original release at the inspected endpoints:
KernelCraft remains empty and the public benchmark head is unchanged. The
[arXiv abstract](https://arxiv.org/abs/2611.02028) still lists v1, and the
[coauthor publication entry](https://jiaeenie.github.io/) links the paper without
a visible code link. The saved scope does not exclude private, other-author,
unindexed, other-branch or future releases. No author was contacted.

The separate [finite source replay](results/finite-trace-v2/results.json) erases
scalar values and executes integer control, source accesses, barriers and
logical collectives for one complete 1,024-thread block:

| Variant | Access records | Classification failures | Final epoch | All threads halt |
| --- | ---: | ---: | ---: | --- |
| Original | 489,926 | 7,081 | 4 | Yes, PC116 |
| Repaired | 475,752 | 0 | 4 | Yes, PC115 |

The canonical conflict is thread0's normalization read at PC102/event273898 and
thread80's write at PC111/event290953. Both access output cell50256 in block
epoch4. The reader's unclamped column51200 is out of bounds, then clamps to50256.
The repair's guard skips that read. The replay preserves every address record
in compressed streams; the independent archive replay compares their complete
decompressed SHA256 hashes and diagnostic records. This finite replay is not a
universal Lean execution theorem or a numerical run.

The initial source checkpoint `31e031c` encoded the abstract seed with denominator
zero. The pinned Lean machine rejects that expression, while the earlier finite
value-erased replay skipped this literal check. Thus those earlier packets do
not establish an executable full kernel. The corrected component packet proves
the reserved positive-denominator seed's evaluation and explicitly rejects a
false claim that the old seed executes. The new finite replay checks the literal
gate and preserves the same complete address traces. Old packets remain frozen
as historical evidence. The GPU HIP sources and numerical input/output bytes
are unchanged by this modeling correction.

```bash
# Lean 4.19.0, standard library only; use fresh output directories.
python3 reproduction/production_softmax/check_program.py --output /tmp/softmax-components
python3 reproduction/production_softmax/replay_components.py \
  --packet /tmp/softmax-components \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-components-replay --lean-bin /path/to/lean-4.19.0/bin
python3 -m unittest discover -s tests -p test_native_softmax.py -v
python3 reproduction/production_softmax/check_prefix.py --output /tmp/softmax-max-prefix
python3 reproduction/production_softmax/replay_prefix.py \
  --packet /tmp/softmax-max-prefix \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-max-prefix-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_first_wave.py --output /tmp/softmax-max-first-wave
python3 reproduction/production_softmax/replay_first_wave.py \
  --packet /tmp/softmax-max-first-wave \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-max-first-wave-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_first_block.py --output /tmp/softmax-max-first-block
python3 reproduction/production_softmax/replay_first_block.py \
  --packet /tmp/softmax-max-first-block \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-max-first-block-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_maximum.py --output /tmp/softmax-maximum
python3 reproduction/production_softmax/replay_maximum.py \
  --packet /tmp/softmax-maximum \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-maximum-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_maximum_stages.py \
  --packet /tmp/softmax-maximum \
  --earlier-packet reproduction/production_softmax/results/max-first-block-v1 \
  --output /tmp/softmax-maximum-stage-guards --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_exp_prefix.py --output /tmp/softmax-exp-prefix
python3 reproduction/production_softmax/replay_exp_prefix.py \
  --packet /tmp/softmax-exp-prefix \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-exp-prefix-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_exp_prefix_stages.py \
  --packet /tmp/softmax-exp-prefix \
  --earlier-packet reproduction/production_softmax/results/maximum-v1 \
  --output /tmp/softmax-exp-prefix-stage-guards --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_reduction_prefix.py --output /tmp/softmax-reduction-prefix
python3 reproduction/production_softmax/replay_reduction_prefix.py \
  --packet /tmp/softmax-reduction-prefix \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v2 \
  --output /tmp/softmax-reduction-prefix-replay --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_softmax/check_reduction_prefix_stages.py \
  --packet /tmp/softmax-reduction-prefix \
  --earlier-packet reproduction/production_softmax/results/exp-wave-v1 \
  --output /tmp/softmax-reduction-prefix-stage-guards --lean-bin /path/to/lean-4.19.0/bin
```

## Finite AMD numerical evidence

Each host ran both full native sources for 25 paired trials: rows1,3,64,255
times six input families, plus the pinned upstream-default 8,192-row dataset.
The smaller families cover seeded normal values, signed zeros,
constant negative values, structured dyadics, a final-cell maximum and wide
alternating values. Each kernel is included verbatim in the HIP driver under an
entry-symbol-only rename. The driver records compiler dependencies, allocation
guards and read-only input preservation. It does not assert that executing the
original source on hardware was race-free.

| Host | Trials / launches | FP64-reference comparisons, both variants | Tolerance failures |
| --- | ---: | ---: | ---: |
| mi350 | 25 / 50 | 1,018,206,820 | 0 |
| mi350-2 | 25 / 50 | 1,018,206,820 | 0 |

Tolerance is `2^-24 + 0.002 * abs(reference)`. The four actual output streams
are byte-identical within each dataset, even though the original has the source-level conflict.
An independent CPU check reproduces the NumPy FP64 stable-softmax formula with
Torch FP64, then checks all stored FP16 reference bits. A further direct check
compares every actual GPU output against the declared
`torch.softmax(inp.float(), dim=1).half()` reference. That also has zero tolerance
failures. The sampled dataset has 937,383 differing FP16 values and maximum
absolute error `1.52587890625e-05`; the upstream-default dataset has 31,823,579
differing values and maximum absolute error `0.00048828125`. Thus this is not
bitwise equivalence to the reference.
Byte-identical streams are checked once per SHA256 and mapped explicitly to all
four host/method names.

The upstream-default dataset has 8,192 rows and 411,705,344 values per method.
Its generator copies the pinned `common.h` random helper bodies, uses
`srand(0)` and the original three-outlier loop, which **multiplies by20** before
the documented FP16 conversion. The generator records its C compiler, libc,
precursor hashes and exact helper bytes. Its CPU reference checks and both-host
full-size numerical audits passed. Each host contributes 823,410,688 comparisons
from that one paired full-size trial, with zero tolerance failures or nonfinite
outputs. Maximum absolute error to the independent rounded FP64 oracle is also
`0.00048828125`.

The [sampled numerical packet](results/sampled-gpu-v1/results.json) and
[full-size packet](results/upstream-gpu-v1/results.json) retain both hosts'
runtime records, original manifests and independent audits. Separate
[sampled](results/sampled-reference-v1/results.json) and
[full-size](results/upstream-reference-v1/results.json) CPU formula checks
regenerate the stored reference bits. Direct GPU-to-Torch checks are retained
for the [sampled](results/sampled-torch-gpu-v1/results.json) and
[full-size](results/upstream-torch-gpu-v1/results.json) datasets. The
[full-size transfer receipt](results/upstream-transfer-v1/results.json) records
the interrupted/resumed download and reconstruction of all four files from one
unique body after checking the original remote hashes and every original
manifest. No output bytes were approximated or regenerated by a kernel.
Independent restoration from the prepared release assets passes every original
input and device manifest for the [sampled](results/sampled-restoration-v1/results.json)
and [upstream-default](results/upstream-restoration-v1/results.json) datasets.

Large raw input/output payloads are published as separate
[release assets](https://github.com/harsh-nod/lark/releases/tag/native-softmax-evidence-20261111);
metadata packets retain the original manifests and compiler inputs. The
[restorer](restore_gpu.py) reconstructs all original input and device streams
losslessly and checks each original manifest before independent numerical audit.
The [publication audit](results/publication-v1/results.json) checks all four
server-side SHA256 digests against the frozen packets, verifies the tag's exact
commit and checks anonymous public access and file lengths. It also downloads
and hashes the complete sampled-output asset without authentication; the other
three public bodies are covered by their server digests and public HEAD checks.
The four compressed assets total 1,593,326,479 bytes. No paid endpoints
or model calls are used. Original NVIDIA results, historical agent runs/token
costs and the authors' unreleased adaptation remain unreproduced.

A [bounded public-artifact recheck](results/max-prefix-artifact-recheck-v1/results.json)
on November 11, 2026 found no original release at the inspected author/org/repository
endpoints or exact-paper repository searches. KernelCraft was still empty and
the inspected benchmark head unchanged. This does not exclude private,
unindexed, other-author, other-branch or future releases.

```bash
gh release download native-softmax-evidence-20261111 --repo harsh-nod/lark \
  --pattern 'native-softmax-*' --dir /tmp/softmax-assets
# Choose either sampled-gpu-v1 or upstream-gpu-v1; use a fresh output directory.
python3 reproduction/production_softmax/restore_gpu.py \
  --packet reproduction/production_softmax/results/upstream-gpu-v1 \
  --assets /tmp/softmax-assets --output /tmp/softmax-restored-upstream
python3 reproduction/production_softmax/audit_gpu.py \
  --input /tmp/softmax-restored-upstream/input \
  --device-output /tmp/softmax-restored-upstream/mi350 --output /tmp/softmax-restored-audit
```

```bash
python3 reproduction/production_softmax/prepare_gpu.py --output /tmp/softmax-input
python3 reproduction/production_softmax/prepare_upstream_gpu.py --output /tmp/softmax-upstream-input
# Copy one prepared directory to each available AMD host, then run there:
python3 /tmp/softmax-input/run_gpu.py --input /tmp/softmax-input --output /tmp/softmax-device
# Retrieve the original device streams/manifests, then audit on a CPU with NumPy:
python3 reproduction/production_softmax/audit_gpu.py --input /tmp/softmax-input \
  --device-output /tmp/softmax-device --output /tmp/softmax-audit
python3 reproduction/production_softmax/audit_torch_gpu.py --input /tmp/softmax-input \
  --mi350 /tmp/softmax-mi350 --mi350-2 /tmp/softmax-mi350-2 --output /tmp/softmax-torch-audit
```
