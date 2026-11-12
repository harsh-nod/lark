# Complete native AWQ GEMM certificate

The `native-awq-gemm-real-v24` profile proves complete initialized native
execution, race freedom of the actual whole trace, and equality of every
extracted output with an independent dense real matrix product. It binds the
complete 138/226-instruction HIP source, layouts, geometry, original fuel and
closed Torch reference to the checked statement. Four source-bound exports
cover `(M,K,N)` = `(17,32,64)`, `(17,32,128)`, `(33,64,192)`, `(33,64,256)`.
The theorem quantifies over every supported shape, input and initial outside
memory; these four exports instantiate its two tile paths and multiple blocks.

Supported dimensions are positive, K is divisible by 32, N by 64, and all matrix
products and launched thread indices satisfy the original signed address
bounds. Block64/wave64, padded shared A16×40 and B32×(tileN+8), both K16 passes,
all K32 iterations, both barriers, row-tail guards and FP32-to-half output
conversions remain in the program. Fuel remains lane512, warp`tileN/8+1`,
block`2*(K/32)+1`, grid1. All new proof modules and generated Main files retain
recursion 10000 and heartbeats 2000000. Only `propext`, `Classical.choice` and
`Quot.sound` occur in successful axiom audits.

The source-order theorem first retains arbitrary scalar operations, including
storage conversions. Output coverage inverts the actual writer and fragment
coordinates and proves that later lanes and blocks preserve every other
output. The trace proof classifies actual accesses throughout all staging,
native operand loads, matrix snapshots, output stores and scheduler resumptions.
Shared writes occur in odd block epochs; shared operand reads occur in even
epochs. Equal locations with unordered writes have the same writer. Starting
from an empty trace discharges race freedom without assuming a safe trace.

The separate exact-real bridge proves that all K32 tiles and their two K16
passes cover each dense dot product exactly once. Its specification is
`sum(j=0..K-1, A[row,j]*B[j,col])` for every output row and column. Half/float
conversions are identities in this interpretation. The certificate gives no
IEEE equivalence or floating-point error bound. Opcode-to-hardware
correspondence and the race-free reduction to hardware interleavings remain
external trust assumptions.

This is an independent AMD adaptation of the pinned vLLM source. It retains
the paper's FP16-weight and single-split-K departures, and uses AMD wave64
16×16×16 MFMA fragments. The authors' adapted NVIDIA PTX, original production
model outcomes, token costs and NVIDIA measurements remain unavailable.
The ninth independently accepted production family does not reproduce the
paper's original nine results.

## Reproduce

Initialize the optional `lean-real` project with its locked Mathlib dependencies
and selected compiled cache. `LARK_REAL_PROJECT` can select an initialized
checkout supplying the nine pinned external dependencies. Lean 4.19.0 is required.

```sh
lark verify-native-awq-gemm \
  reproduction/production_awq_gemm/cases/m17_k32_n64/kernel.hip \
  --reference reproduction/production_awq_gemm/cases/m17_k32_n64/reference.py \
  --task reproduction/production_awq_gemm/cases/m17_k32_n64/task.json \
  --output /tmp/lark-awq-certificate --timeout 180
lark check /tmp/lark-awq-certificate --timeout 180
```

The generic checker rereads the exact source and reference AST, lowers the
program, reconstructs the statement, checks the pinned proof/configuration
sources and closed report types, then reruns Lean. A fully rehashed changed
statement, source, model or configuration is refused.

```sh
python3 reproduction/production_awq_gemm/check_native_real.py \
  --output /tmp/lark-awq-real
python3 reproduction/production_awq_gemm/replay_native_real.py \
  --packet /tmp/lark-awq-real --output /tmp/lark-awq-real-replay \
  --lean-bin /path/to/lean-4.19.0/bin --dependency-project lean-real
python3 reproduction/production_awq_gemm/check_native_real_stages.py \
  --packet /tmp/lark-awq-real --output /tmp/lark-awq-real-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin --dependency-project lean-real
python3 reproduction/production_awq_gemm/check_installed.py \
  --output /tmp/lark-awq-installed --lean /path/to/lean-4.19.0/bin/lean \
  --dependency-project lean-real
```

The [source packet](results/canonical-real-v1/results.json) records all four
exports and independent rechecks, 83 owned Lean modules, 702 library audits
and eight Main audits per export: 734 audit occurrences over 710 distinct
declarations. Nine source mutations and five direct false Lean statements
fail logically. Four changed references and twenty rehashed certificate
changes are refused: 38 negative controls in total. Timeouts and proof-budget
failures do not count as logical rejection.

The [frozen replay](results/canonical-real-validation-v1/results.json) starts
without any owned compiled objects or Git executable on the proof-build path.
It checks all nine external dependency revisions before restricting PATH,
replays the frozen Python reader, rebuilds the complete proof and all four
Main instances, matches all 734 audits and repeats the 14 false Lean claims.
The [scope controls](results/canonical-real-stage-guards-v1/results.json) reject
38 fully rehashed changed reports before archive extraction, including
erased proof flags and missing theorem audits. The
[installed-wheel check](results/installed-wheel-v24-v1/results.json) matches
all 83 required proof resources and SDK files, verifies and rechecks a
certificate outside the checkout, and refuses a rehashed changed statement.

The unchanged [paired GPU evidence](README.md) remains 120 launches over ten
shapes and six input families across both MI350 hosts: 820,224 CPU float64
comparisons, zero failures at `atol=rtol=0.002`, zero cross-host FP16 bit
differences, and 380 FP16-word differences against separately rounded CPU
Torch FP32. Those finite numerical observations remain separate from the
exact-real proof. This proof extension makes no GPU launches or model calls.
Historical component archives retain their original scopes and counts.

The [public source archive](https://github.com/harsh-nod/lark/releases/tag/native-awq-canonical-real-20261112)
is bound to source commit `13fa403b879018d8263876652761d8202fc40efd`.
Its [anonymous-download receipt](results/canonical-real-publication-v1/results.json)
checks all 176 frozen files, binds all 83 proof files and 150 source files to Git,
and rerenders the four complete source instances. The 234,051-byte download
has SHA256 `c473e80dd1ee9b6cba4160371c5c06805ef771fbb165a6a4ddd6199925c6fd6d`
and is byte-identical to the independently rebuilt archive. A second cold
build of the identical download is not counted. The exact-source
[18-job CI run](https://github.com/harsh-nod/lark/actions/runs/43300772965)
is recorded as in progress in that immutable receipt; it is not counted as
passed there.
