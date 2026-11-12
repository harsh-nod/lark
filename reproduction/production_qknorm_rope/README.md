# Native fused Q/K normalization and RoPE development study

This independent adaptation follows the paper's stated out-of-place departure
for `vllm_fused_qknorm_rope`. It reads FP16 QKV `[tokens,48,128]` with Q32/K8/V8
heads, FP16 Q/K weight vectors and already-gathered FP16 cosine/sine rows. It
writes one new `[tokens,40,128]` Q/K buffer. The input, including all V heads,
stays unchanged. Both interleaved and split-half layouts are implemented.

The source is pinned to vLLM
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8`,
[`csrc/fused_qknorm_rope_kernel.cu`](upstream/csrc/fused_qknorm_rope_kernel.cu).
The [provenance](provenance.json) records the independent rewrites, departures
and file hashes. The authors' actual adapted source, parameters, proof project,
model conversations and NVIDIA measurements remain unavailable.

The adaptation retains the native 256-thread block and five blocks per token.
Each logical 32-lane group handles one head, and each lane holds four contiguous
values. Four native wave64s cover eight heads per block. Every input element is
converted to FP32, accumulated in the original per-lane order, reduced by the
five XOR stages at masks16/8/4/2/1 with width32, and multiplied by the RMS scale
and the appropriate weight before rotation. No intermediate half rounding is
inserted between normalization and RoPE. Split-half rotation retains four
cross-lane exchanges, unary negation, and both synchronization points. All
physical waves contain complete adjacent logical groups; no padding is needed.

The [program module](../../lean/Lark/NativeQKNormRopeProgram.lean) declares both
complete source programs: 88 instructions with five shuffles for interleaved,
107 instructions with nine shuffles and two warp barriers for split-half. The
[address module](../../lean/Lark/NativeQKNormRopeAddress.lean) proves native
head/lane mapping, complete output coverage, unique thread ownership, input
bounds, exclusion of V-head reads and signed-int32 bounds for every supported
token count `1..65535`. A footprint theorem derives race freedom under an
explicit actual-access classification premise. It does not discharge that
premise or prove complete execution.

The execution development now checks the actual first 24 scalar instructions,
the sequential 64-lane preparation fold, and all five logical-width-32 XOR
snapshots. Both layouts have a checked scalar continuation from the last
snapshot through the final add, RMS scale, four weight indices, Q/K weight
selection, four weight reads, and eight source-order normalization products.
For split-half, the actual wave scheduler is connected through normalization
to the first warp barrier at PC59. Its four normalized values match the
source-order five-stage reduction expression; its prefix records 512 reads,
preserves memory and epochs, and is race-free from an initial state. That
historical packet retains its prefix scope; the later split-half physical-wave
proof connects the rotary suffix and output stores. The interleaved exact-real proof
and certificate backend are described below.

`check_execution_prefix.py` rebuilds the dependency closure from fresh copied
sources, audits the printed theorem axioms, and binds these partial execution
theorems to both complete translated HIP sources at 1, 3, 256 and 65,535 rows.
The normalization-prefix check builds 30 Std-only modules and checks 245 library
axiom audits plus 104 source-bound audits across those eight instances.
The [frozen prefix packet](results/normalization-prefix-v1/results.json) and
[independent fresh replay](results/normalization-prefix-validation-v1/README.md)
publish the logs, archive and source-commit binding. Both runs checked the same
theorem axiom sets; the replay had no Git executable or seeded owned proof cache.
All ten [CI jobs](https://github.com/harsh-nod/lark/actions/runs/43143732308)
passed for source commit `8bf62f9b3c255212b95b10e70126abfafe2ba84d`;
the [CI receipt](results/normalization-prefix-ci-v1/results.json) binds that run
to the published normalization-prefix evidence.
The historical component packets below retain their original, narrower scope.

The interleaved execution development additionally proves the complete native
physical wave from entry to halt, including both rotary pairs and every FP16
output store. All 256 owned output values match the source-order expression;
the 1,024-access wave trace is classified and race-free from an initial state.
Read-only QKV, weights and gathered cache are preserved, and later lanes
preserve outputs already stored by earlier lanes. `check_interleaved_wave.py`
binds this theorem to the translated sources at all four row counts, retains
the split-half normalization-prefix checks, and rejects four changed-source
claims for a wrong output register, sign, operand order or cache pair.
The fresh check builds 40 Std-only modules and checks 350 library axiom audits
plus 128 source-bound audits across eight layout/row instances, rejecting all
four changed-source claims. The [frozen wave packet](results/interleaved-wave-v1/results.json)
and [archive replay](results/interleaved-wave-validation-v1/README.md) publish
the same checks and two rejected scope promotions. A bounded
[artifact recheck](results/interleaved-wave-artifact-recheck-v1/queries.json)
records the public author/org endpoints and exact-paper searches examined.
All ten [wave CI jobs](https://github.com/harsh-nod/lark/actions/runs/43146980739)
passed at source commit `15fd617473eb78436ced20b1984588de4a3139e1`;
the [wave CI receipt](results/interleaved-wave-ci-v1/results.json) binds that run
to the published physical-wave evidence.
The wave packet retains its original scope; the whole-launch development below
extends the interleaved proof. That historical wave packet registers zero certificates.

The complete interleaved block/grid/launch proof now carries actual memory
through all four waves per block and all five blocks per token. Every output
is extracted in tensor order and equals an explicit source-order expression,
and the full trace contains exactly `tokens * 20480` classified accesses and is
race-free from an initial state. All read-only inputs are preserved. The
`Correct` theorem covers every input and outside-memory function, and a second
theorem covers every state satisfying the fixed satisfiable `StdPre`.

`check_interleaved_launch.py` binds these whole-launch theorems to the complete
translated sources at 1, 3, 256 and 65,535 rows. It retains the earlier eight
layout/row witnesses and adds false interface claims with a shortened grid,
altered fuel or truncated output shape. The complete interleaved result follows
the kernel's arithmetic order; that packet leaves equality to the independent
dense reference as a separate obligation. Its combined-layout whole-kernel flags remain
false because the split-half rotary execution is unfinished.
The fresh launch check builds 47 Std-only modules and checks 416 library axiom
audits plus 156 source-bound audits, rejecting all seven changed source/interface
claims.
The [frozen launch packet](results/interleaved-launch-v1/results.json) and
[independent archive replay](results/interleaved-launch-validation-v1/README.md)
publish matching theorem audits, source bindings and rejection results. Three
fully rehashed scope promotions were rejected before archive extraction.
All ten [launch CI jobs](https://github.com/harsh-nod/lark/actions/runs/43149928895)
passed at source commit `50d16fca030777f7b1c9d9b70b6e5b290b9ef620`;
the [launch CI receipt](results/interleaved-launch-ci-v1/results.json) records the run.

The [exact-real interleaved proof](../../lean-real/LarkReal/NativeQKNormRopeInterleaved.lean)
closes the dense-reference obligation for the complete launch. It first proves
that the five XOR snapshots sum exactly the 128 squares of the thread's own
head. It then connects normalization, Q/K weight selection, interleaved rotation
and cache indexing to independent dense formulas. The final `Correct` theorem
and `StdPre` theorem cover every input, outside-memory function and supported
row count. The four new proof modules use the existing proof resource limits
and only standard Lean axioms. Storage conversions are identities in this
interpretation; no IEEE equality or error bound is claimed.

`verify-native-qknorm-rope` exports the fixed source-bound exact-real profile;
`check` re-translates the HIP, checks the closed reference AST, regenerates the
theorem, validates pinned proof/configuration sources and re-runs Lean. This
interleaved backend retains its original fixed profile. The separate split-half
backend described below binds its own complete launch and dense-reference proof.
Earlier split-half prefix and wave packets retain their original narrower scope.

```bash
python3 -m lark_kernels verify-native-qknorm-rope \
  reproduction/production_qknorm_rope/cases/interleaved/kernel.hip \
  --reference reproduction/production_qknorm_rope/cases/interleaved/reference.py \
  --task reproduction/production_qknorm_rope/cases/interleaved/task.json \
  --output /tmp/fused-qk-real-certificate --timeout 600
python3 -m lark_kernels check /tmp/fused-qk-real-certificate --timeout 600
```

Initialize the pinned optional `lean-real` dependencies and selected Mathlib
cache first, or set `LARK_REAL_PROJECT` to an initialized checkout.
`check_native_real.py` exports and rechecks row counts 1, 3, 256 and 65,535,
checks changed-source refusals in Lean and rejects rehashed source, reference,
model, theorem and scope changes. `replay_native_real.py` rebuilds the frozen
archive without Git or seeded owned compiled objects, using only verified
external dependency sources and their cache. Earlier packets retain their
original narrower claims.

The [real certificate packet](results/canonical-real-v1/results.json) exports
four certificates, checks 454 library and 12 principal axiom audits, and rejects
25 changed-source, reference, output or integrity/scope claims. The
[fresh replay](results/canonical-real-validation-v1/results.json) reproduces all
466 audits, all four row specializations and all eight false Lean claims without
Git or owned compiled caches. Seven additional
[fully rehashed scope promotions](results/canonical-real-stage-guards-v1/results.json)
are refused before archive extraction. The
[downloadable certificates and wheel](results/canonical-real-publication-v1/README.md)
include the [source-commit binding](results/canonical-real-publication-v1/source-binding.json).
The installed wheel also rechecked a certificate outside the repository.

The [split-half physical-wave proof](../../lean/Lark/NativeQKNormRopeSplitWave.lean)
now connects entry, normalization, both actual warp-fence resumes, all four
rotary XOR16 snapshots, the lane-dependent partner sign, four cache/product
groups and all output stores to halt. The proof retains the fixed native fuel
and original HIP bytes. Each of the 256 stored values equals its source-order
expression, the 1,280-access trace is classified and race-free from an initial
state, and all read-only inputs are preserved. Participating warp epochs
advance exactly twice; other threads' state is preserved.
`check_split_wave.py` binds these theorems to the complete translated source at
1, 3, 256 and 65,535 rows, retaining the earlier interleaved prefix witnesses.
It tests changed fences, rotary shuffles, partner signs, cache indexing and
output stores. That historical wave milestone left the split-half block/grid
connection and independent dense-reference equality open and added zero source
certificates.
The [frozen split-half wave packet](results/split-wave-v1/results.json) builds
48 Std-only modules and checks 430 library plus 132 source-bound axiom audits,
rejecting all seven changed-source claims. The
[independent archive replay](results/split-wave-validation-v1/README.md) repeats
the same checks without Git or an owned compiled cache, binds all 119 archived
files to the public source commit and rejects six rehashed scope changes before
extraction. Both kernels and references retain the GPU-tested bytes.

The [complete split-half launch](../../lean/Lark/NativeQKNormRopeSplitCorrect.lean)
now carries the actual wave states through every native block and the complete
grid. Its source-order `Correct` and `StdPre` theorems extract every output and
prove actual-trace race freedom for arbitrary scalar operations, every input and
outside memory. The complete trace contains `tokens * 25600` classified accesses.
Both actual warp-fence resumes remain in the execution; no wave or block state
is reset between folds.

The [split-half dense proof](../../lean-real/LarkReal/NativeQKNormRopeSplitDense.lean)
shows that XOR16 selects the opposite 64-column half of the same normalized
head, with the correct sign and cache column. The
[canonical-real launch proof](../../lean-real/LarkReal/NativeQKNormRopeSplit.lean)
then connects the complete extraction to an independent dense reference for
every supported row count. These proofs retain the existing resource limits
and use only standard Lean axioms.

`verify-native-qknorm-rope` selects the fixed certificate profile from the task's
`rotary_layout`: interleaved uses `native-qknorm-rope-interleaved-real-v20`, and
split-half uses `native-qknorm-rope-split-half-real-v21`. The original v20 proof
closure and certificates remain unchanged. Both profiles require the same
closed Q32/K8/V8, width128, separate-output interface and exact-real arithmetic.
Use the command above with `cases/split-half` to export the split-half profile.
`check_split_real.py` exports and rechecks four row specializations and tests
changed source, reference, model, theorem and scope claims.
`replay_split_real.py` rebuilds the frozen split-half archive without Git or
seeded owned compiled objects, using only verified pinned external dependencies.
The [split-half certificate packet](results/split-real-v1/results.json) exports
four certificates, checks 570 library and 12 principal axiom audits, and rejects
29 changed-source, reference, output or integrity/scope claims. The
[independent rebuild](results/split-real-validation-v1/results.json) reproduces
all 582 audits, all four row specializations and all twelve false Lean claims.
Eight [fully rehashed scope changes](results/split-real-stage-guards-v1/results.json)
are refused before archive extraction. The
[downloadable certificates and wheel](results/split-real-publication-v1/README.md)
include the public source-commit binding and installed-package/legacy-certificate
recheck logs. Across both native rotary layouts, eight source-bound fused-Q/K
certificates are now published. These remain independent adaptations of the
paper's operator and do not reproduce its unavailable original artifacts,
historical model experiments or NVIDIA measurements.

The component study builds six Std-only modules, checks 31 library declarations
and nine source declarations at each of eight layout/row instances (103 axiom
audits), and rejects nine false Lean claims. Its standalone replay rebuilds
without Git or a seeded owned proof cache. Ten fully rehashed scope controls
reject invented complete-launch/reference proofs or certificates before source
extraction. Five unit tests check the closed host/reference boundary, including
preservation of the ordinary HIP reader's synchronization restrictions.

The complete finite interpreter checks 40,960 output expressions and all
184,320 accesses at one and three rows in both layouts. Each result is compared
with an independently indexed source-order reduction tree and rotation. The
packet retains complete access traces and lossless expression DAGs, and rejects
15 source changes. This checks finite source execution; it is not a universal
launch theorem or a dense-reference algebra proof.

Both AMD hosts completed 48 paired trials, or 96 launches each, at rows1/3/64/256
with six input patterns and both layouts. The comparison retains the selected
upstream kernel body, common helpers and conversion header; packed conversions
remain in that comparison. Frozen official Torch headers provide its FP16
carrier. Every allocation has 128-byte guards, all adapted inputs and position
IDs are checked unchanged, and upstream V heads are checked unchanged. The
complete compiler-reported include/source closure is captured.

Fresh CPU float64 and Torch FP32 references check **79,626,240 output values**
with zero failures at `atol=rtol=0.002` and zero adapted/upstream bit differences.
The FP16 bits of 3,948 audited output values differ from rounded Torch FP32
results; these comparisons pass tolerance.
Six fully rehashed numerical controls reject a wrong output, invented proofs or
certificate, a missing trial and a widened tolerance without new GPU launches.

**Complete native execution, classification of its universal actual trace and
dense-reference equality remain pending.** This development issues zero source
certificates and is outside the immutable v19 paper ledger. As in the paper,
IEEE/rounding/error guarantees are outside formal scope. This independent
adaptation does not reproduce an original production acceptance or model result.

The frozen [component packet](results/components-v1/results.json),
[independent replay](results/components-validation-v1/results.json),
[scope guards](results/component-stage-guards-v1/results.json) and
[finite values/traces](results/symbolic-v1/results.json) retain the checked
statements and complete finite expression DAGs. The
[both-host packet](results/native-v1/results.json) and
[six numerical controls](results/numerical-controls-v1/results.json) retain the
runtime and CPU audit results. Full raw inputs, output streams, compiler captures
and binaries are in the
[public release](https://github.com/harsh-nod/lark/releases/tag/native-qknorm-rope-evidence-20261111).
All ten [CI jobs](https://github.com/harsh-nod/lark/actions/runs/43112261267) passed
at source revision `c9a7a242de6696e4c9c1aa402d7046b3db2518d9`.
The [publication receipt](results/publication-v1/results.json) binds all 70
archived source files to that revision and records full anonymous downloads of
all four release assets: 111,245,855 bytes matched the local hashes and GitHub's
server digests. It also binds all six evidence manifests and the passing CI
responses.

```bash
# Python3.11+ and Lean/Lake4.19.0; use fresh output directories.
python3 -m unittest discover -s tests -p test_native_qknorm_rope.py -v
python3 reproduction/production_qknorm_rope/check_program.py --output /tmp/fused-qk-components
python3 reproduction/production_qknorm_rope/check_execution_prefix.py \
  --output /tmp/fused-qk-execution-prefix --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/check_interleaved_wave.py \
  --output /tmp/fused-qk-interleaved-wave --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/check_interleaved_launch.py \
  --output /tmp/fused-qk-interleaved-launch --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/replay_components.py \
  --packet /tmp/fused-qk-components --output /tmp/fused-qk-replayed \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/check_component_stages.py \
  --packet /tmp/fused-qk-components --output /tmp/fused-qk-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/run_symbolic.py --output /tmp/fused-qk-symbolic

# Input preparation and independent CPU audits need NumPy and CPU PyTorch.
python3 reproduction/production_qknorm_rope/prepare_gpu.py --output /tmp/fused-qk-input
# Copy the whole frozen input to each free gfx950/wave64 host first.
HIP_VISIBLE_DEVICES=0 python3 /tmp/fused-qk-input/run_gpu.py \
  --input /tmp/fused-qk-input --output /tmp/fused-qk-host
python3 reproduction/production_qknorm_rope/audit_gpu.py --input /tmp/fused-qk-input \
  --host /path/to/mi350 --host /path/to/mi350-2 --output /tmp/fused-qk-audit
python3 reproduction/production_qknorm_rope/check_gpu_controls.py --input /tmp/fused-qk-input \
  --host /path/to/mi350 --output /tmp/fused-qk-numerical-controls
```
