This study independently selects SGLang's
`rmsnorm_cta_double<16384,false,fp16_t>` at
[`fc32cbff6983c7573f4b60eab8b44815668130a0`](https://github.com/sgl-project/sglang/blob/fc32cbff6983c7573f4b60eab8b44815668130a0/python/sglang/kernels/jit/csrc/elementwise/rmsnorm.cuh).
The paper authors' adapted source and source revision are unknown. This is
intermediate evidence for an independent reproduction; it does not reproduce
the paper's original SGLang verification claim.

The selected packed double-load path supports width 16384 with 1024 threads.
The generic CTA path in this revision supports widths only through 8192.
Twelve unmodified upstream files, including helper definitions and the Apache
license, are retained under `upstream/`; `provenance.json` pins their SHA256 and
Git blob IDs. The fixed upstream logical warp width is 32 on both CUDA and HIP.
The closed adaptation embeds those groups in AMD wave64, specializes contiguous
FP16 input/output and weight, disables PDL, and scalarizes vector operations.
Rows range from 1 through 131072 with fixed fuel `(512,8,3,1)`.

The adaptation retains all input vector preloads followed by all weight
preloads, private half caches across both barriers, eight paired square
additions per thread, both five-stage XOR reductions, thirty-two separate shared
inverse slots, and conversion of all output cache cells before the final
stores. It preserves `acc + (x*x + y*y)` grouping and each logical warp's own
inverse slot. It does not replace those operations with a mathematically
equivalent reduction or reload global buffers after the barriers.

`cases/native_original` retains the selected source's unguarded
`partial[warp] = sum` writes by all 32 lanes. These produce 15872 conflicting
write pairs per row in the access model, including writes whose values may be
equal. `cases/native_fixed` explicitly adds a lane-zero guard to that one store.
This repair is separate from the original source and has no conflicting access
pairs in the finite checked launches. This finding about the independently
selected revision does not establish a defect in the paper authors' adaptation.

Current evidence:

The [development proof](SECOND_REDUCTION_PROGRESS.md) now establishes complete
initialized guarded **block** execution: both reductions and barrier resumptions,
all output loops, source-ordered output values and a race-free actual trace.
Its 77 Std-only modules contribute 689 library axiom audits. Whole-grid
composition, exact-real equality and new source-bound certificate/replay packets
remain outstanding. The published packets below retain their original scopes.

- The complete original and repaired sources translate to 109 and 110 IR
  instructions. Six source instances bind both programs, geometry, global,
  shared and private layouts, and fixed fuel for rows 1, 3 and 131072.
- Seven Lean modules provide 36 library axiom audits and 66 source instance
  audits. They establish output coverage, unique output writers, signed address
  bounds, private half-cache bounds and thread ownership, and race freedom
  conditional on the guarded footprint. The only proof axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- Actual `execute` calls establish an original conflicting store pair and a
  guarded two-lane instruction tail **from an explicit cut state**. They do not
  establish initializer reachability, full source execution or classification
  of a whole actual trace. No complete source certificate is issued.
- Complete finite symbolic execution checks rows 1 and 3 for both variants:
  131072 output expressions and 1323648 access events in total. Independently
  indexed source-order expression DAGs agree with all outputs; read-only input
  and weight remain unchanged and all threads halt after two barriers.
- Eleven changed-source controls and eleven false Lean claims are rejected.
  Fresh source-only replay uses no Git executable or owned compiled cache;
  fourteen fully rehashed metadata controls reject unsupported proof claims
  before archive extraction.

The checked packets are in `results/components-v1`,
`results/component-validation-v1`, `results/component-stage-guards-v1`,
`results/symbolic-v1` and `results/finite-controls-v1`. These stage names preserve
their original scope when later proof stages are added. Those component packets
do not establish complete initialized Lean execution, actual whole-trace
classification or exact-real source/reference equality. The component
packets contain no model calls or GPU trials. The later paired-host numerical
study below records GPU execution separately.

The latest published `results/native-wave-partial-v1` stage proves a complete native
physical wave reaches its first block-barrier visit: all five logical32 XOR
snapshots, all five ordered additions, and the actual original or guarded
shared stores execute successfully. The universal theorem covers every physical
wave in every supported row count, arbitrary arithmetic operations and input,
and carried state with incoming PC0 lanes and read-only global buffers. It
requires no safety premise for earlier trace. Source instances bind both full
programs at rows1,3,131072 with unchanged `(512,8,3,1)` fuel.

Every lane reaches PC55 in the original or PC56 in the repair. Its register0
retains the source-ordered five-round value; both sixteen-cell half caches and
native indices survive. The original records all 64 partial writes. The repair
records exactly the two logical leaders, native lanes0 and32, in distinct shared
slots. Their traces add 5184 or 5122 events respectively to unchanged earlier
trace. No barrier is resumed, so synchronization epochs remain unchanged.

The original race witness now belongs to **actual initialized native execution**:
lanes0 and1 reach conflicting writes to the same shared partial slot. This holds
for arbitrary arithmetic and input, including coincident stored values. The
repaired initialized wave's entire actual trace satisfies `Good` and is
race-free. These claims concern the independently selected source adaptation,
not the authors' unavailable adapted kernel text or source revision.

Forty-three modules contribute 346 library axiom audits, and six complete-source
instances contribute twenty each, for **466 audits**. Eighteen false source or
execution claims are rejected logically. The independent frozen replay in
`results/native-wave-partial-validation-v1` runs without Git or owned compiled
caches. Twenty-nine fully rehashed controls in
`results/native-wave-partial-stage-guards-v1` reject unsupported completion,
barrier-resumption, race, cache, trace, fuel and certificate claims before source
extraction. New proof modules retain maxRecDepth10000/maxHeartbeats2000000;
no source, machine, fuel or shape bounds are raised.

This stage leaves whole-block convergence and barrier resumption outside its
checked scope. It does not cover the second reduction, inverse storage, second
barrier, output phase, whole launch or canonical-real reference equality. The
development proof above extends through the complete guarded block. This stage issues zero
source certificates and makes no original paper/model/NVIDIA reproduction claim.
The [publication check](results/native-wave-partial-publication-v1/results.json)
binds all 128 frozen source files to commit
`df39d5aa8440cda658247a9a5835e09074856b9e` and verifies five anonymous public
downloads byte for byte. A [clean-checkout wheel check](results/native-wave-partial-wheel-v1/results.json)
compares all 43 required Lean resources and all 37 native SGLang modules with
their published sources. The [CI run](https://github.com/harsh-nod/lark/actions/runs/43209285830)
passes all fifteen jobs, including all earlier proof/replay gates. The
[complete receipt](results/native-wave-partial-ci-v1/results.json) binds the
unchanged proof sources, workflow and contract tests to that checked revision.

The earlier `results/native-wave-entry-v1` stage proves successful execution of
all sixty-four lane preparations followed by the first logical32 XOR snapshot.
Both complete source variants bind at rows 1, 3 and 131072. The universal theorem
covers every native physical wave of every supported row count, arbitrary
arithmetic operations and input, and carried machine state with read-only
global buffers and PC0 for the incoming lanes. It requires no safety premise
for the earlier trace. The resulting state is at PC45 with each lane's own
sum in register0 and its mask16 peer's sum in register1, both private half caches
intact, and the two logical32 partitions still separate. Exactly 5120 new access
events precede the unchanged earlier trace. The snapshot changes no memory or
epochs. The native warp-runner transition uses the unchanged `(512,8,3,1)` fuel.

Thirty-three modules and six source instances pass 356 axiom audits, and eleven
false source/execution claims are rejected. Independent frozen-source replay in
`results/native-wave-entry-validation-v1` uses no Git or owned compiled caches.
Twenty-two fully rehashed controls in `results/native-wave-entry-stage-guards-v1`
reject claims about completed reductions, shared stores, barriers, complete
execution and reference equality before extraction. New loop invariants use
induction and local control of definition unfolding; proof limits remain
maxRecDepth10000 and maxHeartbeats2000000. The remaining four XOR snapshots,
five additions, shared stores, barriers, full launch and real-reference equality
remain outstanding. This stage issues no source certificate.

`results/gpu-compilation-v1` freezes and hashes a three-method HIP comparison:
the original adaptation, guarded repair and verbatim selected upstream template
body with explicit HIP helpers. Both `mi350` and `mi350-2` compile the identical
driver for gfx950 with contraction disabled. Compilation does not execute a GPU
trial or establish CUDA helper/compiler equivalence. The subsequent numerical
study executes those same three methods.

The [paired-host numerical audit](results/native-gpu-v1/gpu-audit.json) passes
all **190,513,152 CPU float64 comparisons** at `atol=rtol=0.002`. Each host runs
24 cases at rows1,3,64,255 and width16384: random normal, signed zero, constant,
structured dyadic, half rounding/subnormal and mixed-magnitude inputs. That is
**144 launches** across the three methods and both hosts. Every allocation
canary and read-only input/weight bit survives; each output starts as NaN.
Every method and both hosts produce identical bits in these finite cases.
The separate freshly recomputed CPU Torch FP32 reference differs in **1,734
comparisons**, retained by trial in the report; no IEEE equivalence is claimed.
These equal numerical outputs do not erase the original access-model race.

All thirteen [fully rehashed numerical controls](results/numerical-controls-v1/results.json)
are rejected, including one wrong value, a missed final store in each of the
three methods, widened tolerance, missing methods/trials, changed inputs,
occupied-GPU records and unsupported proof/completion claims. The strict GPU
check requires at least 98% free memory and 0% activity. The
[prelaunch history](results/native-gpu-v1/mi350-prelaunch-history.json) records
two `mi350` attempts stopped at 1% activity before source-kernel execution.
The successful attempt initializes the runtime first, observes three idle
samples, and executes the unchanged frozen runner in that same process;
its own strict guard also passes.

The [four release assets](https://github.com/harsh-nod/lark/releases/tag/native-sglang-rmsnorm-evidence-20261112)
retain all frozen FP16 operands, all three complete output streams per host,
compiled binaries, every compiler-reported source/header, independent audit
sources and numerical controls. Repository
[metadata and hashes](results/native-gpu-v1/results.json) bind every asset.
Numerical checks issue zero source certificates and make no original paper
model/token-cost or NVIDIA reproduction claim.
All four assets were [downloaded anonymously and replayed](results/native-gpu-publication-v1/results.json),
76,562,395 bytes matching local checksums and GitHub server digests. Outside the
checkout with Git unavailable, both the CPU audit and all thirteen rejection
controls reproduced their result JSON byte for byte. That replay ran no GPU
kernels or model calls.

`results/native-wave-entry-publication-v1` binds all 110 frozen proof-source
files to commit `6b2850ffa5fe73de8ac8a1345be46b064554f71c` and records five
anonymous public downloads whose bytes match the committed packets.
The [clean-checkout wheel check](results/native-wave-entry-wheel-v1/results.json)
compares all 33 required Lean resources and all 27 native SGLang modules byte
for byte, including the newly packaged general trace-transport module.
The [dedicated CI receipt](results/native-wave-entry-ci-v1/results.json) records
the native SGLang job passing its source checks, fresh proofs, independent
replays and rejection controls at the same proof revision. Its captured full-run
job list retains the status of the other regression jobs.
The later [complete CI receipt](results/native-wave-entry-all-ci-v1/results.json)
records all fifteen jobs passing, with unchanged proof sources, workflow and
contract tests in the published evidence revision.

The earlier `results/first-shuffle-v1` stage proves successful native scalar
execution from the standard initializer through PC44, the first logical32 XOR
shuffle, with unchanged lane fuel512. The universal theorem covers every valid
thread at every supported row count, arbitrary arithmetic operations, input and
initial outside memory. It executes all input and weight preload loops and all
eight paired-square additions in their source order. It extracts all thirty-two
raw input/weight cache values and the accumulated thread sum, preserves global
read-only buffers and epochs, and classifies all eighty actual prefix memory
events to prove this prefix race free. It stops before executing the shuffle.
Twenty-three modules and six source instances pass 224 axiom audits; ten false
source and execution claims are rejected. `results/first-shuffle-validation-v1`
rebuilds the frozen proof without Git or owned compiled caches; eighteen fully
rehashed controls in `results/first-shuffle-stage-guards-v1` reject unsupported
claims about later shared stores, barriers, whole execution and reference
equality before extraction. These results strengthen the earlier prefix
equation stage below and still issue no source certificate.
`results/first-shuffle-publication-v1` byte-binds all 95 frozen source files to
`4f6c2ee5a4452ceb9331bd55bdcd0b28b8fe86bf` and verifies five anonymous public
downloads. Those bytes match the independently replayed local packet; the
public-download check does not execute another replay.
`results/first-shuffle-ci-v1` records all fifteen CI jobs passing at that same
source commit, including the successful-prefix proof, independent replay and
scope guards. It binds all 95 source archive files and makes no claim about
later native wave execution.

The additional `results/input-preload-prefix-v1` stage proves a scalar prefix
equation for the first 128 executed instructions, through PC16 before weight
preloads, for both complete programs and arbitrary arithmetic operations. The
resulting explicit state contains all sixteen raw input half-cache values,
preserves read-only global buffers, and accounts for sixteen global reads plus
sixteen private writes. Fourteen modules and six source instances pass 140
axiom audits; six false source/cache claims are rejected. The prefix equation
equates the remaining `runLane` continuations. It does not establish successful
execution through the first shuffle or reachability of the later partial-store
cut state. This distinction is explicit in its report.

`results/input-preload-validation-v1` repeats that check from frozen source
without Git or owned compiled caches. Fifteen fully rehashed controls in
`results/input-preload-stage-guards-v1` reject claims about weight preloads,
continued lane success, the later cut state, complete execution and reference
equality before extraction. `results/component-ci-v1` records the passing
dedicated component CI job at `4d082a49bdcd7e89ec7527153c5b447f2beb74fc`
and byte-binds all 75 files in that earlier component source archive to Git.
`results/components-complete-ci-v1` records all fifteen repository CI jobs
passing at that component commit; it does not claim CI coverage of later stages.
`results/input-preload-complete-ci-v1` records all fifteen jobs passing at the
later input-preload prefix commit `ff0d169c7b45bbe4f76abeb5b2c1bf6ab0056414`
and byte-binds its 83 archived source files. The first-shuffle CI run is tracked
separately at its own source commit.

From the repository root, with Lean/Lake 4.19.0 installed:

```sh
python3 -m unittest discover -s tests -p test_native_sglang_rmsnorm.py -v
python3 reproduction/production_sglang_rmsnorm/check_program.py \
  --output /tmp/lark-sglang-components --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_components.py \
  --packet /tmp/lark-sglang-components --output /tmp/lark-sglang-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_component_stages.py \
  --packet /tmp/lark-sglang-components --output /tmp/lark-sglang-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/run_symbolic.py \
  --output /tmp/lark-sglang-symbolic
python3 reproduction/production_sglang_rmsnorm/check_controls.py \
  --output /tmp/lark-sglang-finite-controls
python3 reproduction/production_sglang_rmsnorm/check_input_preloads.py \
  --output /tmp/lark-sglang-input-preloads --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_input_preloads.py \
  --packet /tmp/lark-sglang-input-preloads --output /tmp/lark-sglang-input-preload-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_input_preload_stages.py \
  --packet /tmp/lark-sglang-input-preloads --output /tmp/lark-sglang-input-preload-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_prefix.py \
  --output /tmp/lark-sglang-first-shuffle --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_prefix.py \
  --packet /tmp/lark-sglang-first-shuffle --output /tmp/lark-sglang-first-shuffle-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_prefix_stages.py \
  --packet /tmp/lark-sglang-first-shuffle --output /tmp/lark-sglang-first-shuffle-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_wave_partial.py \
  --output /tmp/lark-sglang-wave-partial --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_wave_partial.py \
  --packet /tmp/lark-sglang-wave-partial --output /tmp/lark-sglang-wave-partial-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_wave_partial_stages.py \
  --packet /tmp/lark-sglang-wave-partial --output /tmp/lark-sglang-wave-partial-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_wave_entry.py \
  --output /tmp/lark-sglang-wave-entry --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_wave_entry.py \
  --packet /tmp/lark-sglang-wave-entry --output /tmp/lark-sglang-wave-entry-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_wave_entry_stages.py \
  --packet /tmp/lark-sglang-wave-entry --output /tmp/lark-sglang-wave-entry-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
```

Each command requires a fresh output directory. The dedicated
`native-sglang-rmsnorm` CI job reruns these gates from source.
