# Recorded full-wave reduction results

The `wave-sum-real-v16` source-bound certificate proves the whole native wave64
HIP butterfly against all 64 independently translated reference cells. Its
final theorem covers every real input and outside-memory state, actual launch
completion and race freedom. A fresh global `lark check` passed. All six printed
certificate audits use only `propext`, `Classical.choice` and `Quot.sound`.

Four direct Lean controls were rejected without resource failures. They bypass
the Python profile preflight: a wrong last shuffle fails program equality, a
changed last reference cell fails cell equality, adding one to every reference
cell fails canonical-reference equality, and block 128 fails the actual-launch
interface. These are fixed equality/interface checks, not reproductions of the
paper's original mutant set or diagnosis-channel census.

| Evidence per host | `mi350`, physical GPU 2 | `mi350-2`, physical GPU 0 |
| --- | ---: | ---: |
| Native wave64 kernel launches | 272 | 272 |
| Outputs compared bitwise with the source expression tree | 17,408 | 17,408 |
| Source-tree bit differences | 0 | 0 |
| Ordinary numerical trials / CPU Torch comparisons | 264 / 16,896 | 264 / 16,896 |
| Ordinary failures at `atol=rtol=1e-5` | 0 | 0 |
| Maximum ordinary absolute error | 2.384185791015625e-7 | 2.384185791015625e-7 |
| Cancellation trials / output values | 8 / 512 | 8 / 512 |
| Cancellation outputs disagreeing with CPU Torch beyond tolerance | 128 | 128 |
| Maximum cancellation absolute error | 1 | 1 |

The ordinary dataset contains 64 one-hot basis vectors, 128 seeded dyadic
vectors, 64 seeded normal vectors and eight structured patterns. Cancellation
probes place `2^25`, `-2^25` and `1` at eight fixed triples of input positions.
All GPU results match the source tree bit for bit, including those probes.
Reassociation changes rounded results, and the 128 disagreements are retained
as floating-point scope evidence. They are **excluded from ordinary numerical
passes**. No claim of universal floating-point equivalence follows from the
exact-real proof or this finite experiment.

The numerical reference is the executed CPU Torch source. Separately, serial
FP32 evaluation of its mathematical reference AST differs bitwise from Torch
in 3,840 outputs across the dataset. That stream is archived too: the formal
AST is interpreted over reals, and no bitwise Torch equivalence is claimed.

Both hosts ran the gfx950-targeted binary and reported native warp 64. Every trial used separate
allocations with 128-byte guards on each side, poisoned outputs, and an input
preservation check. All recorded guards and inputs remained unchanged. Fresh
preexecution activity checks and a 98% free-VRAM runtime guard passed.

The frozen source, CPU certificate/control files, generated packet and two
raw GPU archives are in `results/`. `summary.json` comes from independently
regenerating the source-bound statements and all numerical inputs before
auditing both raw output streams. No model calls or paid endpoints were used.

A fully rehashed one-bit output alteration is rejected at the actual raw
source-tree comparison. The installed wheel freshly checks the certificate
outside the repository, and the standalone exported Lake project rebuilds from
its sources against the pinned dependencies. The previous PTX, shuffle and MFMA
evidence audits and the historical paper-source audit also replay successfully.

This adds one independent full-wave reduction certificate and numerical study.
It does not reproduce an original optimized production kernel, original model
pass rate, NVIDIA timing or the paper's complete results. The
[paper coverage ledger](../COVERAGE.md) retains those dependencies explicitly.
