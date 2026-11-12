# Second reduction proof checkpoint

This development checkpoint extends the published `native-wave-partial-v1`
packet. It is not a whole-kernel certificate or a reproduction of the paper's
original SGLang experiment.

`Lark.NativeSglangRmsNormWaveSecond.native_second_wave` proves successful native
wave64 execution from the guarded adaptation's reached first-block resumption
through the second reduction to the second block barrier (PC76). It retains all
64 physical lanes in the native runner: the first 32 lanes execute all five XOR
snapshots, ordered additions, mean/epsilon/rsqrt, and distinct shared stores;
the upper 32 lanes park at PC76. The proof quantifies over arbitrary scalar
operations and retains lane-specific values without reassociation.

Its dependency chain also proves that all 16 native waves reach the first block
barrier from initialized execution, records the 32 shared partial values, and
resumes that barrier. The original adaptation's reached first-phase conflict
and the guarded first-phase race freedom are proved separately from successful
execution.

Validation:

```sh
cd lean
lake build Lark.NativeSglangRmsNormWaveSecond
```

The checked root has 56 owned Std-only modules and 468 library axiom audits.
Every new module keeps recursion 10000 and heartbeats 2000000; no machine fuel or
shape bound was increased. Audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

Remaining work includes carrying second-phase completion through the other 15
waves and the block scheduler, resuming the second block barrier, all output
loops, whole-grid correctness and actual trace classification, exact-real
reference equality, and a fresh source-bound frozen packet with independent
replay and rejection controls. The existing published packet, source-instance
audit counts, and 15 passing CI jobs apply to the earlier first-barrier scope;
they do not validate this stronger development checkpoint.

The previously published 144 AMD numerical launches are unchanged. This
checkpoint runs no new GPU trials or model calls.
