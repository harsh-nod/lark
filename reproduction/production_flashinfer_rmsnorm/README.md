# Native FlashInfer RMSNorm development study

This independent adaptation instantiates FlashInfer's actual
`flashinfer::norm::RMSNormKernel<8,__half>` at width16,384. The
[pinned upstream header](upstream/flashinfer-norm.cuh) is from
`bc29697ba20b7e6bdb728ded98f04788e16ee021`, the exact FlashInfer dependency
of the previously selected SGLang revision. This is an independent source
selection; the authors' adapted file and original upstream revision are unknown.
The [provenance](provenance.json) records the source hashes and changes.

The adaptation preserves the native 1,024-thread block, two rounds of eight
contiguous FP16 components per thread, the ordered per-thread square sum,
logical32 XOR reductions at masks16/8/4/2/1, 32 shared partials, both block
barriers, and the second first-logical-warp reduction. It reads input and weight
without modifying them and writes a separate FP16 output. The weight-bias zero
addition and final cast remain explicit. The paper's literal thread-count and
`rsqrtf` departures are retained. HIP executes complete logical32 cohorts
inside physical wave64; that architecture adaptation is recorded separately.

The closed development interface accepts contiguous `[rows,16384]` input and
output, weight`[16384]`, and rows`1..131072`. The last permitted scalar index is
exactly `2^31-1`; no larger signed-int32 address is accepted. The original
ordinary task parser retains its own limits. Parsing this interface does not
register or issue a certificate.

The [program](../../lean/Lark/NativeFlashInferRmsNormProgram.lean) fixes the
complete 68-instruction translation, both barriers and PC67 halt. The
[address module](../../lean/Lark/NativeFlashInferRmsNormAddress.lean) proves
column coverage, unique native output ownership and int32 bounds for every
supported row count. Its race-freedom theorem requires an explicit `Good`
classification for every actual access. The later
[whole-launch theorem](../../lean/Lark/NativeFlashInferRmsNormCorrect.lean) now
derives that classification from the actual source scheduler, proves termination
and extracts every output for arbitrary value operations. The separate
[dense exact-real theorem](../../lean-real/LarkReal/NativeFlashInferRmsNorm.lean)
proves that the reduction covers every input square and the complete output
matches weighted RMSNorm's independent dense formula.

The new `native-flashinfer-rmsnorm-real-v22` profile issues **four checked source
certificates** at rows1,3,64,131072; its theorem covers all supported row counts
and arbitrary real inputs/outside memory. The 68-module proof closure contains
490 library axiom audits and eight audits per source instance (522 in total).
All 25 negative checks passed: eight false Lean claims, four altered references,
and thirteen fully rehashed file/scope changes. The kernel, reference, task,
upstream pin, fixed fuel and published GPU results are unchanged.
The exact-real interpretation uses identity storage conversions, as disclosed
for this proof model; it does not assert an IEEE accuracy or error bound.

```sh
python3 -m lark_kernels verify-native-flashinfer-rmsnorm \
  reproduction/production_flashinfer_rmsnorm/cases/native_16384/kernel.hip \
  --reference reproduction/production_flashinfer_rmsnorm/cases/native_16384/reference.py \
  --task reproduction/production_flashinfer_rmsnorm/cases/native_16384/task.json \
  --output /tmp/flashinfer-certificate --lean /path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels check /tmp/flashinfer-certificate --lean /path/to/lean-4.19.0/bin/lean --timeout 600
```

These commands use the optional exact locked Mathlib packages/cache from
`lean-real`; `LARK_REAL_PROJECT` may select an initialized dependency checkout.
Owned proof sources are compiled and source-checked separately.

The earlier [first-block execution proof](../../lean/Lark/NativeFlashInferRmsNormBarrier.lean)
now derives the actual scheduler execution through the first barrier for every
supported shape and arbitrary value operations. It composes all sixteen native
waves without resetting memory, proves all thirty-two partial values, preserves
every global cell, classifies the generated trace and proves its race freedom.
The actual barrier continuation advances every participating thread to PC32 and
block epoch one. The fixed fuel remains `(512,8,3,1)`. These declarations use
the standard Lean kernel with recursion 10,000 and heartbeat limit 2,000,000.
At that checkpoint, the second reduction, normalization, output execution,
complete launch and reference equality were unfinished. Its frozen receipt
issues no certificate; the later whole-launch profile above supplies those
independent proof obligations without changing the original paper result status.

The [first-block checker receipt](results/first-block-v1/results.json) records a
fresh thirty-module source closure and audits 225
library declarations plus twelve declarations at each of six source instances
(297 audits). It also checks eleven false Lean claims. The
[independent replay](results/first-block-validation-v1/results.json) passed with
neither Git nor an owned compiled cache; all fourteen
[fully rehashed scope controls](results/first-block-stage-guards-v1/results.json)
rejected claims about unfinished later stages before extracting any source. The older component and
GPU evidence below retain their original scope and source pins.
The [publication receipt](results/first-block-publication-v1/results.json)
records 42 anonymously downloaded public files (291,957 bytes), all matching
commit `adbc0c83cb8dba4b59c683414e7c074f4875f998`. All ninety archived source
files match proof-source commit `2e44acc3e101e07614cf30abf7bf4e1bff1e4f23`.
The separate frozen-source replay passed; the public download itself did not
execute another replay. [CI](https://github.com/harsh-nod/lark/actions/runs/43173986851)
was still running at this checkpoint.

```sh
python3 reproduction/production_flashinfer_rmsnorm/check_execution.py \
  --output /tmp/flashinfer-first-block --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_flashinfer_rmsnorm/replay_execution.py \
  --packet /tmp/flashinfer-first-block --output /tmp/flashinfer-first-block-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_flashinfer_rmsnorm/check_execution_stages.py \
  --packet /tmp/flashinfer-first-block --output /tmp/flashinfer-first-block-guards \
  --lean-bin /path/to/lean-4.19.0/bin
```

The [fresh component check](results/components-v1/results.json) rebuilds six
Std-only modules, audits 21 library and five source declarations per instance,
and binds the complete source, signature, shared layout, geometry and fuel at
rows1,3,64,255,65535,131072: **51 axiom audits** in total. Nine false Lean claims
are rejected logically rather than by resource exhaustion. One changed-width
control is a false fixed-program-identity claim; rejection does not establish
that every different width is numerically incorrect. The
[independent replay](results/components-validation-v1/results.json) rebuilds
the archived sources without Git or a seeded owned compiled cache. Ten
[fully rehashed scope controls](results/component-stage-guards-v1/results.json)
refuse invented execution, reference and certificate claims before extraction.

The [finite symbolic check](results/symbolic-v1/results.json) executes all
threads at one and three rows, compares **65,536 output expressions** against
an independently indexed source-order formula, retains **266,500 accesses**,
and checks every halt, barrier epoch and read-only input. Interned shallow
tuples compare the exact expression DAG without expanding the large reduction
tree at every output. Compressed DAGs, output IDs and complete traces are
published. Nine changed sources fail expression, initialization or access
checks. These are finite Python checks. Complete source proofs remain pending.

Both `mi350` and `mi350-2` completed 24 paired trials, or 48 launches per host,
at rows1,3,64,255. The comparison retains the selected upstream template body
verbatim and substitutes explicit HIP shuffle, rsqrt and scalar-vector helpers.
It uses `-ffp-contract=off`, captures every compiler-reported source/header,
checks 128-byte allocation guards and preserves all input/weight bits. Outputs
start as NaNs, so a missed store fails the numerical audit.

The [fresh numerical audit](results/native-v1/gpu-audit.json) recomputes every
dense CPU float64 reference and a separate CPU Torch FP32 reference from the
frozen FP16 operands. All **127,008,768 float64 comparisons** pass at
`atol=rtol=0.002`; each method's output streams match across hosts. Adapted and
upstream outputs have **3,422,543 signed-zero differences and 264 other one-ULP
differences per host**, with no nonzero sign disagreements. The
[rounding analysis](results/native-v1/rounding.json) retains every affected
trial and its maximum magnitude difference. All nine
[fully rehashed numerical controls](results/numerical-controls-v1/results.json)
are rejected, including a wrong output, an unwritten final output, missing
trials, widened tolerance and invented IEEE/proof/completion claims.

The [four release assets](https://github.com/harsh-nod/lark/releases/tag/native-flashinfer-rmsnorm-evidence-20261112)
retain all frozen inputs, both complete output streams from each host, compiler
captures, binaries, standalone audit sources, component proof packets and finite
traces. Use those full packets with `audit_gpu.py`; the
[repository metadata](results/native-v1/results.json) retains their reports and
hashes. These numerical checks add no source certificates or complete execution
theorems.

```bash
python3 -m unittest discover -s tests -p test_native_flashinfer_rmsnorm.py -v
python3 reproduction/production_flashinfer_rmsnorm/check_program.py \
  --output /tmp/flashinfer-components --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_flashinfer_rmsnorm/replay_components.py \
  --packet /tmp/flashinfer-components --output /tmp/flashinfer-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_flashinfer_rmsnorm/check_component_stages.py \
  --packet /tmp/flashinfer-components --output /tmp/flashinfer-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_flashinfer_rmsnorm/run_symbolic.py \
  --output /tmp/flashinfer-symbolic
```

The [publication check](results/publication-v1/results.json) binds all 58 archived
source files to commit `7097c674b132baf7e6477b5b5481d0ada0268a8d`. It anonymously
downloaded 47 source/finite-packet files (3,089,408 bytes), matched their committed
bytes, and replayed all 51 axiom audits and nine false Lean claims from the public
source archive. No owned compiled cache or Git executable was used for replay.
The dedicated [FlashInfer CI job](https://github.com/harsh-nod/lark/actions/runs/43164561966)
passed; the complete thirteen-job run was still in progress at publication capture.
The later [complete CI receipt](results/components-ci-v1/results.json) records
all thirteen jobs passing at source commit `7097c674b132baf7e6477b5b5481d0ada0268a8d`.
It verifies unchanged component sources, workflow and contract tests at the
published component-evidence commit. GPU execution is validated separately by
the paired-host packet above.

All four numerical release assets were
[downloaded anonymously and replayed](results/native-publication-v1/results.json):
56,262,937 bytes matched both the committed checksums and GitHub's server
digests. Outside the checkout, with Git unavailable, the CPU audit, rounding
analysis and all nine numerical controls reproduced their reports byte for
byte. That public replay executed no GPU kernels or model calls.

Original paper model/token-cost results
and NVIDIA measurements remain separate missing inputs. This development uses
zero model calls and does not mark the paper's FlashInfer result reproduced.
