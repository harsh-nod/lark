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
classification for every actual access. Deriving that classification from
complete source execution remains work, as do the whole-launch and exact-real
reference theorems. There are **zero registered source certificates**.

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
checks. These are finite Python checks, not universal proofs. Paired-host
numerical validation and complete source proofs remain pending.

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

The new CI job repeats these checks. Original paper model/token-cost results
and NVIDIA measurements remain separate missing inputs. This development uses
zero model calls and does not mark the paper's FlashInfer result reproduced.
