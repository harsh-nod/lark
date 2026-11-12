# Historical native whole-block development proof

`Lark.NativeSglangRmsNormCompleteBlock` now proves successful execution of the
guarded adaptation from initialized native block state through both reductions,
both block-barrier resumptions, every output loop and halt at PC109. The proof
covers every supported row count and arbitrary scalar operations, inputs and
outside memory. It retains the full physical wave64 runner, logical32 shuffle
partitions, the fixed `(512,8,3,1)` execution fuel and all recorded accesses.

Every thread writes its 16 source-ordered output halves. Private raw input and
weight caches are preserved through scaling, conversion occurs at the source's
explicit half operations, and the global copy loop copies the resulting halves
without another conversion. Inverse values remain lane-specific for arbitrary
scalar operations. No arithmetic reassociation is assumed.

Successful execution, output values and complete trace classification are
proved separately. Execution requires no incoming trace-safety premise. The
complete initialized guarded block's actual trace is race-free. The reached
original first-phase conflict remains a separate theorem about the unguarded
adaptation. Neither finding identifies the paper authors' unavailable adapted
source text or revision.

Validation:

```sh
cd lean
lake build Lark.NativeSglangRmsNormCompleteBlockFrame
```

The historical checked root at commit `b71a51f659a1fea71400fc522c95d272d05a9180`,
including frames for other blocks, had 77 owned Std-only modules and 689 library
axiom audits. That receipt retains its original proof bytes.
All new modules retain recursion 10000 and heartbeats 2000000. No machine fuel,
shape bound, stack limit or numeric proof limit was raised. The audits use only
`propext`, `Classical.choice` and `Quot.sound`. CI checks this development root
and rejects warnings, build failures and unsupported proof axioms.
The [development receipt](results/native-block-development-v1/results.json)
records a successful isolated rebuild from copied source with no project cache
at the start or Git metadata. It includes all 77 source hashes and 689 distinct
axiom audits. The separate frame check used a Lean-only executable path. This
source-only library check is separate from a frozen complete-source replay.

The later [canonical-real profile](CANONICAL_REAL.md) extends this development
through the complete native grid and dense mathematical reference. It exports
four complete-source certificates, checks source/reference/tamper controls,
freezes a new source packet and verifies an installed wheel. The original
whole-block receipt remains a development checkpoint with its original scope;
it is not retroactively relabeled a whole-kernel certificate. The published
`native-wave-partial-v1` packet, its six source instances and independent replay
also retain their earlier first-barrier scope. No original-paper result is
claimed by these independent adaptations.

The previously published 144 AMD numerical launches are unchanged. This
checkpoint runs no new GPU trials or model calls.
