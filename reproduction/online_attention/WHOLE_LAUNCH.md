# Native attention whole launch and dense real reference

The independently adapted native FP16 source now has complete machine
execution, actual-trace race freedom and extraction proofs for every permitted
group count (`1..65535`). It retains N=128, D=256, block32/wave64 geometry,
all 91 source instructions, all shared/private arrays and the unchanged fuel.
Four separately checked exports bind the actual source IR, layout, geometry
and fuel to canonical dense real SDPA at groups 1, 3, 64 and 65535.

The source remains byte-identical to the paired [MI350 numerical validation](NATIVE.md).
This checkpoint adds no GPU trials or model calls. It does not recover the
authors' original optimized PTX, historical model pass rates/token costs,
NVIDIA timings or engineering-effort measurements.

## Actual execution and source order

`LarkNativeAttention.source_order_correct` proves the original scalar machine's
complete `Correct` relation for all scalar operation interpretations, inputs
and initial outside memory. Every native block executes all nine phases:
initialization and first K/V copy, four query-computation phases, three later
K/V copies and the final halt phase. Each block resumes eight barriers. All
threads halt at source PC 90; all declared outputs are extracted and the
complete actual trace passes the machine's race check.

Each query phase computes four query rows per lane, each with 32 complete
256-component score products and 256 complete 32-term weighted-V sums. The
proof preserves the old-output half load, intermediate half stores, private
maximum/mass reads and stores, arithmetic grouping and denominator division.
No algebraic identities are assumed in this abstract-operator theorem.

Each lane executes 1,914,303 source instructions across the nine phases:

| Part | Instructions per lane |
| --- | ---: |
| Initialization and first K/V copy | 5,405 |
| Query preparation over four key tiles | 16,468 |
| All score loops | 922,656 |
| All exponential/denominator loops | 3,120 |
| Old-state selections and rescalings | 152 |
| All weighted-V/output loops | 962,576 |
| Private-state/query-counter tails | 64 |
| Query-loop exit guards | 4 |
| Three later K/V copies | 3,855 |
| Final key increment and halt guard | 3 |

The unchanged per-phase lane budget is one million instructions. The longest
phase requires 476,262; later copy phases require 1,285. The full grid proof
preserves completed blocks' outputs and untouched blocks' program counters
and epochs while subsequent blocks execute.

The [dependency-free frozen packet](results/native-whole-launch-v1/results.json)
freshly builds 84 local Lean modules, binds source identity and audits 174
principal theorem dependencies. Twenty-nine false claims are refused,
including wrong next-tile values, missing halt/counter updates, incorrect grid
outputs, output extraction length and race-check results. These are scoped
claim controls, not the original paper's mutation benchmark. An
[independent archive replay](results/native-whole-launch-validation-v1/results.json)
rebuilds all local modules from an empty directory. The previous first-key
source files and all 121 audits pass unchanged.

## Canonical real interpretation

`LarkReal.NativeAttention.correct` connects the actual full launch to an
independent dense specification. Each score is a 256-component Q/K dot product
divided by 16. All 128 key positions appear once, in order. Each output is the
dense exponential-weighted V numerator divided by the dense exponential sum.
The proof allows arbitrary real scores and signed values and proves every
online denominator positive.

The real proof first identifies the source's ordered dot, exponential and
weighted-V folds with finite sums. It connects the actual first-key branch and
each later update to the normalized online invariant, then flattens the four
32-key tiles into the independent 128-key dense reference. The final theorem
uses actual `runLaunch`, actual trace race freedom and actual output extraction.

Storage conversions are identities **only in this real interpretation**. This
does not prove IEEE FP16/FP32 equivalence, compiler floating-point contraction
equivalence or a floating-point error bound. The separate AMD numerical packet
retains all measured rounding differences and tolerance checks.

The [canonical-real frozen packet](results/native-canonical-real-v1/results.json)
freshly builds 91 local modules (including five real modules) against the exact
locked Mathlib revision, audits 17 universal/export results and checks four
source-bound specializations. Four scoped controls reject an omitted final
halt, wrong private layout, wrong native block size and false dense output.
A [separate archive replay](results/native-canonical-real-validation-v1/results.json)
checks the source hashes, dependency pins, fresh build, exports and controls.
All proof dependencies are standard `propext`, `Classical.choice` and
`Quot.sound`; no extra axioms or skipped kernel checks are used.

```bash
# Lean 4.19.0; these output directories must be outside Git:
python3 reproduction/online_attention/check_native_prefix.py --stage whole-launch --output /tmp/native-whole-launch
# Initialize the pinned lean-real package/cache as in CI, then:
python3 reproduction/online_attention/check_native_real.py --output /tmp/native-canonical-real
```

Both frozen source archives have standalone build instructions. Earlier lane,
block, weights, output and first-key packets remain unchanged. The ordinary
verification reader still has its original array bounds and memory-space
restrictions; this native source uses its separately scoped development reader
and source-bound export checker.
