# Native first-query output prefix

This checkpoint joins the [weight computation](WEIGHTS.md) to the first query
row's complete 256-column output update for the first key tile. It checks the
unchanged 91-instruction native FP16 attention source with block32/wave64
geometry and `[groups,128,256]` inputs. It adds **zero whole-source attention
certificates**.

`first_output_initial_prefix` quantifies over every permitted group count
(`1..65535`), active block and member lane, scalar type and operation
interpretation, input and outside memory. It joins the actual first `runBlock`
phase and barrier resume to the actual `runLane` continuation from PC 21 through
119,060 instructions to PC 83. The candidate contains the checked output value
at every one of the lane's 256 first-query columns, preserves declared inputs,
and has a race-free actual prefix trace.

PC 83 is the continuation before the private maximum/mass stores. The theorem
states `runLane (extra + 119060) resumed = runLane extra candidate`; it does not
claim a halt, a parked barrier, a complete block phase or a complete launch.

| Part | Source instructions per lane |
| --- | ---: |
| Query preparation, score dot products, exponentials and denominator | 58,891 |
| First-key old-state selection and rescaling | 8 |
| 256 output columns, including the exit guard | 60,161 |
| Joined continuation from PC 21 to PC 83 | 119,060 |

Each column retains the ordered 32-term weighted-V sum. The proof uses the
actual shared-weight and shared-V reads, the old global-output read, the
`fromHalf` conversion, both rescaling terms, denominator division and final
`toHalf` store. It preserves the source's arithmetic grouping, including the
different multiplication orders in denominator and old-output rescaling.
It assumes no commutativity, real-number identities or IEEE error bounds.

The output-loop invariant preserves unread old outputs until their own column
is processed. The first-key branch explicitly avoids private-state reads; the
first block proof supplies the source-initialized zero output cells. The
generic output-loop lemmas also handle the subsequent-key branch when its
per-thread prior maximum and mass are available. Execution of later key tiles
is not yet joined.

The [frozen packet](results/native-output-prefix-v1/results.json) builds the
closed 57-module Lean import graph from fresh files outside Git, binds the
translated source IR/layout/geometry/fuel and audits 61 principal results.
Only standard `propext`, `Classical.choice` and `Quot.sound` are admitted.
Fourteen false postconditions are refused, including incorrect weighted-V
accumulation, half-output stores, first-query output values, initial key
counters and continuation PCs. These are scoped claim controls; they do not
reproduce the authors' mutation benchmark.

```bash
python3 reproduction/online_attention/check_native_prefix.py --stage output --output /tmp/native-output
# Lean 4.19.0, in the extracted frozen archive:
lake build
lake env lean Main.lean
```

The other fourteen top-level Lean files intentionally fail at false claims.
A [separate archive replay](results/native-output-validation-v1/results.json)
rebuilds from an empty directory and rechecks source hashes, binding, axiom
audits and controls. Earlier lane, block and weights packets remain unchanged.

Private-state stores, later query rows, all later key tiles, complete block/grid
scheduling and canonical dense-reference equality remain unfinished. The
source remains byte-identical to the paired [MI350 numerical validation](NATIVE.md).
This checkpoint adds no GPU trials or model calls and no original-paper
completion claims. Original author artifacts, historical model pass rates and
token costs, H100 timings and engineering-effort measurements remain unavailable.
