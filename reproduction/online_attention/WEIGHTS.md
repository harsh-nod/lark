# Native first-query scores and exponential denominator

The native attention proof now joins the [first block phase](BLOCK.md) to each
lane's first query-row preparation, all 32 score dot products, maximum updates,
in-place exponentials and ordered denominator accumulation. The unchanged
source has 128×256 inputs per group, block32/wave64 geometry and four key tiles.
The joined initial-state result covers the first query row and first key tile.
It adds **zero whole-source attention certificates**.

`first_weights_initial_prefix` quantifies over every permitted group count
(`1..65535`), active block and member lane, scalar type and operation
interpretation, input and initial outside memory. It joins the actual first
`runBlock` reduction and block-barrier resume to a `runLane` continuation
reduction through PC 56. The resulting candidate state has the checked maximum,
all 32 exponential weights, their ordered denominator sum, preserved declared
inputs and a race-free actual prefix trace.

PC 56 is a continuation point. The theorem states:

```text
runLane (extra + 58891) resumed = runLane extra candidate
```

It does not assert that execution halts or parks at PC 56. The remaining source
must still execute through output updates and the next block barrier.

The source instruction count is checked component by component:

| Part | Instructions per lane |
| --- | ---: |
| First query setup and 256 query loads | 1,030 |
| 32 score dot products, stores, maximum updates and exit guard | 57,666 |
| Exponential/denominator setup, 32 updates and exit guard | 195 |
| Continuation from PC 21 to PC 56 | 58,891 |

Each score dot product retains the 256-component source multiplication and
addition order, followed by multiplication by `ops.literal 1 16`. The first
score initializes the maximum; later scores use `ops.max`. Each score cell is
then overwritten with `ops.exp (ops.sub score maximum)`. The in-place loop's
invariant keeps unread original scores distinct from transformed cells. The
denominator retains the source's ordered addition fold starting at
`ops.literal 0 1`. These facts quantify over arbitrary scalar operations; no
IEEE identities, error bound or dense-reference equality are assumed.

`NativeAttentionQuery*`, `ComputeReady`, `Dot*`, `Score*`, `Exp*` and `Weights`
under `lean/Lark/` implement the proof components. Small state-transfer lemmas
and an explicit arithmetic equality for the fuel counts let the kernel check
their composition without expanding the entire intermediate state history.
No kernel checks are skipped and no extra axioms are introduced.

The [frozen checkpoint](results/native-weights-prefix-v1/results.json) freshly
rebuilds the closed 43-module Lean import graph outside Git, binds the translated
source IR/layout/geometry/fuel, and audits 37 principal theorem dependencies.
All dependencies are standard `propext`, `Classical.choice` and `Quot.sound`.
Nine false postconditions are refused, including the wrong continuation PC,
an incorrect exponential weight and an incorrect denominator. These are scoped
claim controls, not the paper's original mutation benchmark.

```bash
python3 reproduction/online_attention/check_native_prefix.py --stage weights --output /tmp/native-weights
# With Lean 4.19.0, after extracting the frozen source archive:
lake build
lake env lean Main.lean
```

The archive's nine other top-level Lean files intentionally fail at false
assertions. A [separate archive replay](results/native-weights-validation-v1/results.json)
rebuilds that archive from an empty directory and rechecks its source hashes,
binding and controls. The earlier lane and block frozen packets are unchanged.

Old running-state selection, weighted V products, global output updates, later
query/key tiles, complete block/grid scheduling and canonical-reference equality
remain unproved. The source is byte-identical to the existing paired
[MI350 numerical validation](NATIVE.md); this checkpoint adds no hardware trials
or model calls. It does not recover missing author artifacts, historical model
pass rates/token costs or H100 timings.
