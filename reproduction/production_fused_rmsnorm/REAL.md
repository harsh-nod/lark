# Canonical-real native fused add RMSNorm

The [real theorem](../../lean-real/LarkReal/NativeFusedRmsNorm.lean) connects
the complete seeded-inout native launch to an independent two-output formula.
For every row, let `x[j] = input[j] + residual[j]`. The normalized output is
`x[j] / sqrt(sum(x*x)/16384 + 1e-5) * weight[j]`; the residual output is `x[j]`.
The extractor returns all normalized values, then all residual values.

The theorem covers every input and initial outside memory for all rows1..255,
width16384, block1024, physical wave64 and logical32 reductions. It uses the
actual source initializer, complete native scheduler, both block barriers,
all stores and final halt. Race freedom follows from the actual trace.

The algebra proof constructs the five-stage XOR reduction tree and checks its
leaves are a permutation of each logical32 group. It joins the32 group sums,
the1024 thread sums, both vector rounds and all16384 columns. It then connects
the normalization and residual results to the reference. It assumes no
floating-point reassociation identity: the real interpretation supplies ordinary
real addition and multiplication, with half conversions interpreted as identities.

The [source-bound certificate profile](../../lark_kernels/native_fused_rmsnorm_certificate.py)
checks the closed Torch reference AST, exact source readback, emitted instruction
list, initialized mutable buffers, layout, launch geometry and fuel. Its Lean
statement is `LarkInOutPartition.Correct`, including the seeded precondition and
both extracted output buffers. The ordinary uninitialized-output relation is
not used for this in-place kernel.

The [frozen proof packet](results/canonical-real-v1/results.json) records four
source certificates at rows1/3/64/255, rechecks through `lark check`, changed-source
and reference controls, direct Lean refusals and rehashed artifact/scope controls.
Its27 checks include19 refusals,497 library axiom audits and10 source-certificate
audits, each using only Lean standard axioms. It includes all71 local Lean
modules, the locked Mathlib revision, frozen Python
reader, both-output source/reference/task, proof logs and reproducible source archive.
The [independent archive replay](results/canonical-real-validation-v1/results.json)
starts with no own compiled Lean objects, checks external dependency revisions,
replays the frozen reader and rebuilds with Git unavailable on subprocess PATH.
It repeats all four specializations and eight direct Lean rejection controls.
The [compatibility receipt](results/canonical-real-compatibility-v1/results.json)
checks all six earlier generators and their complete proof-source closures remain
byte-identical. The [wheel audit](results/canonical-real-packaging-v1/results.json)
checks all71 proof-source files and the new profile module are packaged byte-for-byte.
The [ordinary suite](results/canonical-real-tests-v1/results.json) passed165 tests
with9 optional real tests skipped; the new real profile is checked separately
by the27-check runner. CI checks that runner and the frozen archive replay in
a separate `fused-real` job. Earlier frozen packets retain their original claims.

The source is unchanged from the [paired AMD validation](README.md#finite-amd-results).
Those numerical trials and finite comparison tolerances remain separate evidence.
The real theorem supplies no IEEE equivalence or numerical error bound, upstream
API coverage, original paper artifacts, historical model results or H100 timings.

```bash
# Initialize the locked optional Mathlib dependencies/cache in lean-real first.
python3 -m lark_kernels verify-native-fused-rmsnorm \
  reproduction/production_fused_rmsnorm/cases/native_16384/kernel.hip \
  --reference reproduction/production_fused_rmsnorm/cases/native_16384/reference.py \
  --task reproduction/production_fused_rmsnorm/cases/native_16384/task.json \
  --output /tmp/fused-real-certificate
python3 -m lark_kernels check /tmp/fused-real-certificate --timeout 600
python3 reproduction/production_fused_rmsnorm/check_native_real.py \
  --output /tmp/fused-real-checks
python3 reproduction/production_fused_rmsnorm/replay_native_real.py \
  --packet /tmp/fused-real-checks --output /tmp/fused-real-replay \
  --lean-bin /path/to/lean-4.19.0/bin --dependency-project lean-real
```
