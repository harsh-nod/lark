# Complete guarded native RMSNorm certificate

The `native-sglang-rmsnorm-real-v23` profile binds the complete 110-instruction
HIP adaptation, its launch, global/shared/private layouts, fixed fuel and the
closed Torch reference to a checked Lean statement. The adaptation independently
instantiates SGLang's packed `rmsnorm_cta_double<16384,false,fp16_t>` path at
upstream revision `fc32cbff6983c7573f4b60eab8b44815668130a0` and explicitly guards
the first reduction's shared store with `lane == 0`.

For every row count from 1 through 131072, every input and weight, and arbitrary
initial outside memory, the proof establishes successful execution of the
actual complete guarded native launch, race freedom of its complete recorded
trace, and equality of every extracted output with the dense weighted RMSNorm
reference. The reference sums all 16384 original input squares, divides by
16384, adds `1/100000`, takes the reciprocal square root, and multiplies the
original input and column weight. The exact-real interpretation makes storage
conversions identities; IEEE rounding is outside this formal claim, as in the
paper.

The proof retains block1024, physical wave64, logical32 shuffle partitions,
both reductions, both barrier resumptions, all three private half[16] caches,
the source's paired accumulation order, the inverse slots and every output
loop. Arbitrary scalar operations first yield the exact source-ordered result,
including lane-specific inverses. Separate real-arithmetic lemmas establish
that both reduction trees cover the dense row exactly once and that every
logical warp uses the canonical inverse. Execution is not premised on a safe
incoming trace. Initialization and trace classification are proved separately.

The machine and frontend are unchanged. Execution fuel remains `(512,8,3,1)`;
all six new proof modules retain recursion10000 and heartbeats2000000. General
projection and transport lemmas avoid expanding constructed machine states
while checking proofs. They change neither execution nor theorem statements.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed in axiom audits.

## Reproduce the certificate

Initialize the optional `lean-real` project with its locked Mathlib dependencies
and selected compiled cache, and make Lean4.19.0 available. `LARK_REAL_PROJECT`
can select another initialized checkout supplying only those pinned external
dependencies. The managed proof cache checks all owned source and compiled
object hashes before reuse.

```sh
lark verify-native-sglang-rmsnorm \
  reproduction/production_sglang_rmsnorm/cases/native_fixed/kernel.hip \
  --reference reproduction/production_sglang_rmsnorm/cases/native_fixed/reference.py \
  --task reproduction/production_sglang_rmsnorm/cases/native_fixed/task.json \
  --output /tmp/lark-sglang-certificate --timeout 600
lark check /tmp/lark-sglang-certificate --timeout 600
```

The checker re-reads and lowers the source, checks the closed single-output
reference AST, compares the complete emitted program and statement, and reruns
Lean against the pinned proof sources. Rehashing a changed source, model,
statement or configuration does not bypass these checks. Report fields and
types are closed; unsupported completion claims are rejected.

The study checker exports rows1,3,64,131072 and independently rechecks each
certificate. Twelve source mutations and six direct false Lean claims must fail
logically. Four changed references and eighteen rehashed certificate changes
must be refused at their proper gates. A timeout or resource-limit failure does
not count as a logical rejection.

```sh
python3 reproduction/production_sglang_rmsnorm/check_native_real.py \
  --output /tmp/lark-sglang-canonical-real
python3 reproduction/production_sglang_rmsnorm/replay_native_real.py \
  --packet /tmp/lark-sglang-canonical-real \
  --output /tmp/lark-sglang-canonical-real-replay \
  --lean-bin /path/to/lean-4.19.0/bin --dependency-project lean-real
python3 reproduction/production_sglang_rmsnorm/check_native_real_stages.py \
  --packet /tmp/lark-sglang-canonical-real \
  --output /tmp/lark-sglang-canonical-real-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin --dependency-project lean-real
```

The frozen replay starts with no owned compiled objects and no Git executable
on its proof-build path. Only the nine source-checked pinned external packages
and their compiled caches are supplied. It replays the frozen reader, rebuilds
the entire proof and first Main, checks the other three Main instances, and
reruns all eighteen false Lean claims. Thirty-two fully rehashed scope controls
must be rejected before archive extraction.

## Checked evidence

The [source-checker packet](results/canonical-real-v1/results.json) contains four
verified and rechecked source certificates, 88 owned Lean modules, 750 library
axiom audits and eight Main audits for each instance: 782 audit occurrences and
758 distinct declarations. All 48 recorded checks pass their expected outcomes:
eight positive checks, eighteen logical Lean rejections and twenty-two boundary
refusals. The source-only archive freezes all proof sources, the reader and Main
instances. Its 428.8-second first export includes the fresh library build and
fits the unchanged 600-second limit.

The [scope-guard packet](results/canonical-real-stage-guards-v1/results.json)
records all 32 rehashed overclaims rejected before extraction. The
[installed-wheel packet](results/installed-wheel-v23-v1/results.json) matches all
88 required proof resources byte for byte and verifies/rechecks a certificate
from the installed package outside the checkout. This managed-cache check is
separate from a fresh frozen-source rebuild without owned compiled objects.

## Relation to the paper and earlier evidence

This is independent adaptation evidence. The paper authors' adapted source,
revision and original model dialogues are unavailable in this study; their
original SGLang model/token result is not claimed reproduced. The reached
unguarded conflict remains a separate theorem about the independently selected
adaptation. The published first-barrier packets retain their narrower original
scope and are not retroactively relabeled whole-launch certificates.

The earlier paired-host numerical study retains 144 AMD launches and
190513152 CPU-float64 reference comparisons with zero tolerance failures. Those
GPU measurements are separate from this proof; the proof checker and replay
make no model calls or new GPU launches. Their original numerical artifacts are
unchanged.
