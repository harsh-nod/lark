# Native attention first block phase

The native FP16 attention proof now composes all 32 lanes in the original
block32/wave64 scheduler and resumes the first block barrier. This extends the
[lane prefix](PREFIX.md). **It is still a partial execution proof, with zero
whole-source attention certificates.** The later [compute checkpoint](WEIGHTS.md)
extends this result through the first query row's scores and denominator.
Output computation, later phases and canonical dense-reference equality remain unproved.

`first_block_from_initial` quantifies over every permitted group count
(`1..65535`), every active block, every scalar type and operation interpretation,
every input and arbitrary initial outside memory. It proves that the actual
first warp fold in `runBlock` converges at the source barrier at PC 20 with:

- All 32 lanes at the same barrier, with their native indices retained.
- All 32,768 output cells owned by that block initialized to
  `ops.toHalf (ops.literal 0 1)`.
- All 8,192 K cells and 8,192 V cells in the first shared tile copied from the
  corresponding input cells using `ops.fromHalf`.
- Every declared input unchanged and the actual prefix trace passing the
  original machine's race check.

`first_block_step` proves the next actual scheduler reduction:

```text
runBlock (extra + 1) start = runBlock extra (firstResumed start)
```

It assumes readable declared inputs, initial PC 0 for the block and an active
block index. No alternative scheduler or logical-wave wrapper is introduced.
`first_resumed_pc` and `first_resumed_epoch` prove that every member reaches
PC 21 and its block epoch increments once. The tile values, initialized outputs,
input cells, native indices and already recorded access conditions survive
the resume. Initial epoch zero therefore becomes one before the shared K/V reads.

The four added modules are `NativeAttentionFirstFrame`, `FirstFold`, `FirstBlock`
and `FirstResume` under `lean/Lark/`. Frame lemmas preserve peer state and cells
while each lane executes. The fold proof then joins the unchanged `runLane`
calls, followed by actual `runWarp`, convergence and block resumption.
All audited theorem dependencies are standard `propext`, `Classical.choice`
and `Quot.sound`; there are no additional axioms or skipped kernel checks.

The [frozen report](results/native-block-prefix-v1/results.json) rebuilds the
25-module local Lean import closure outside Git, freshly binds source IR,
array layout, native geometry and fuel, and audits 16 principal theorems.
Six false postconditions are refused: the earlier three lane assertions and
three block assertions covering a wrong resumed PC, an omitted epoch increment
and an incorrect copied key. These are scoped controls, not the paper's original
mutation benchmark. `source.tar.gz` includes all Lean sources, binding and controls.

```bash
python3 reproduction/online_attention/check_native_prefix.py --stage first-block --output /tmp/native-block
# After extracting the frozen source archive, with Lean 4.19.0:
lake build
lake env lean Main.lean
```

The six other top-level Lean files in the archive intentionally fail at false
assertions. The [archive replay](results/native-block-validation-v1/results.json)
rebuilds that exact archive in another empty directory and rechecks its hashes,
binding and controls. The earlier lane-only frozen packet is unchanged.

The HIP source remains byte-identical to the [paired MI350 validation](NATIVE.md).
This checkpoint adds no GPU trials or model calls, proves no IEEE equivalence
or numerical error bound, and does not reproduce the authors' missing original
attention adaptation, historical model outcomes or H100 timings.
