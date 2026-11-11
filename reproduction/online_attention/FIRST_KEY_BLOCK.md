# Native first-key block computation

This checkpoint joins the actual native initialization to a complete first-key
block computation: all four query rows for each of 32 lanes, all 32,768 output
stores and all private maximum/mass stores, followed by the second block
barrier and its actual resume. It retains the full 91-instruction source,
block32/wave64 geometry, `[groups,128,256]` inputs and the unchanged machine
fuel. It adds **zero whole-source attention certificates**.

`first_key_block_initial` quantifies over every allowed group count
(`1..65535`), active block, scalar type and operations, input and initial outside
memory. It checks the actual `runWarp` lane fold, block convergence and resume
for both phases. Its candidate has PC 88, key index zero and block epoch two
for every member lane, all expected first-key outputs and private online state,
unchanged declared inputs and a race-free actual prefix trace.

The scheduler reduction is:

```text
runBlock 9 initial = runBlock 7 candidate
```

PC 88 is the continuation that increments the key index before the next K/V
copy. The candidate has not completed attention. Seven block phases remain:
three K/V copy phases, three query-computation phases and the final halt phase.

The source query phase fits the unchanged one-million-instruction lane budget.
The proof returns a successful `some` state parked at the real PC 87 block
barrier before the scheduler resumes it. The checked instruction counts are:

| First-key query phase, per lane | Instructions |
| --- | ---: |
| Query-index setup and four query preparations | 4,117 |
| Four complete score loops | 230,664 |
| Four exponential/denominator loops | 780 |
| Four old-state selections and rescalings | 32 |
| Four 256-column weighted-V/output loops | 240,644 |
| Four private-state stores/query-counter tails | 16 |
| Final query-loop exit guard | 1 |
| Total | 476,254 |

The generic query phase also proves the subsequent-key case in 476,262
instructions when its K/V tile, old outputs and private maximum/mass are
available. This includes the actual private reads on subsequent keys. The
first-key case avoids those reads. All scalar arithmetic grouping, ordered
dot/denominator folds and half-conversion sites remain explicit. No real-number
identities, IEEE equivalence or floating-point error bound are assumed.

The composition proves that each row preserves the old values needed by other
rows. Each lane preserves peers' control state, output cells and private state;
K/V tiles remain intact throughout the query phase. Generic scalar-machine
expression, instruction and lane-execution frame lemmas support the scheduler
proof. No kernel checks are skipped and no extra axioms are introduced.

The [frozen packet](results/native-first-key-block-prefix-v1/results.json)
freshly builds 73 Lean modules, binds translated source IR/layout/geometry/fuel
and audits 121 principal theorem dependencies. Only standard `propext`,
`Classical.choice` and `Quot.sound` are admitted. Twenty-one false claims are
rejected, including a wrong last-row output, omitted private stores, the wrong
subsequent-key instruction count and an incorrect second resume PC/epoch.
These scoped claim controls do not reproduce the authors' mutation benchmark.

```bash
python3 reproduction/online_attention/check_native_prefix.py --stage first-key-block --output /tmp/native-first-key-block
# Lean 4.19.0, inside the extracted frozen archive:
lake build
lake env lean Main.lean
```

The other twenty-one top-level Lean files intentionally fail at false claims.
A [separate empty-directory archive replay](results/native-first-key-block-validation-v1/results.json)
rechecks source hashes, binding, audits and controls. The earlier output-stage
sources and audits also pass unchanged; previous frozen packets are preserved.

The three later K/V copy/query phases, final halt, complete block/grid launch
and dense-reference equality remain unfinished. The full source is unchanged
from the paired [MI350 numerical validation](NATIVE.md). This checkpoint adds
no GPU trials, hosted or local model calls, original author artifacts,
historical pass rates/token costs, H100 timings or engineering-effort results.
