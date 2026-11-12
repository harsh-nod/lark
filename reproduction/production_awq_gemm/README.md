# Native AWQ GEMM reproduction

The independent AMD FP16 adaptation has [complete source certificates](REAL.md)
for initialized native launch execution, actual whole-trace race freedom,
output extraction and dense exact-real matrix-product equality. All four
source-bound exports verify and recheck. The original scheduler, native matrix
snapshots, fuel and guarded FP32-to-half output stores are retained. This
brings independent accepted production-family coverage to nine. Paired
numerical validation and finite symbolic execution remain separate evidence;
the original paper's results are still not fully reproduced.

The source is pinned to vLLM
[`83f5de4`](https://github.com/vllm-project/vllm/blob/83f5de466a889c29ac5fbfbe342d6fe4c09811e8/csrc/quantization/awq/gemm_kernels.cu).
[Provenance](provenance.json) records its Git blob, SHA256 and Apache license.
The paper's departures are retained: FP16 weights replace int4 dequantization,
one split-K iteration is used, and block-decode sizes are literals. The paper
transcribed the upstream inline assembly to PTX. This independent port maps
the matrix fragments to native AMD wave64 `f32_16x16x16f16` MFMA. Its output
ownership and matrix-instruction shape therefore differ from NVIDIA's two
logical32 warps and `m16n8k16` instructions. The authors' exact adapted PTX is
still a missing input.

Both N64 and N128 paths retain the upstream padded shared arrays, guarded A
row tails, two block barriers per K32 chunk, two K16 matrix passes, accumulator
flow and FP16 output conversion. Shared A has 640 half cells; shared B has
2304 or 4352. The FP16 shared extension is confined to this reader. The older
generic shared-memory limit is unchanged.

| Check | Result |
| --- | --- |
| Complete source binding | Four 138/226-instruction sources match the fixed Lean template, including every matrix site, barrier and store |
| Complete real certificates | Four verified/rechecked exports; 83 owned modules, 702 library audits and 32 Main audits, 734 total; only `propext`, `Classical.choice`, `Quot.sound` |
| Complete correctness | Universal initialized `runLaunch`, actual whole-trace race freedom, all output extraction and independent dense real equality under the original shape/fuel contract |
| Universal arithmetic | Shared/global bounds, writer inversion, fragment coordinates, signed scalar bounds and `grid*64 ≤ M*N` |
| Initial execution | Actual full-program `runLane` executes all 31/47 setup instructions; all 64 lanes converge and the first block barrier resumes through the existing scheduler |
| Guarded A staging | Both complete eight-iteration loops, row guard and join: 35/36 scalar instructions; all eight shared values, input preservation, outside-memory frame and exact 8/16-event trace length |
| B staging | All four/eight chunks and eight elements per chunk, 158/314 scalar steps; every staged B value, input preservation, outside-memory frame and 64/128 trace events |
| Combined lane staging | Actual A-then-B order reaches the middle barrier in 193/194 or 349/350 scalar steps using the original lane512 fuel; both value families and all accumulators/epochs retained |
| Complete block staging | All 64 actual lane executions, middle convergence and barrier resumption; initial block execution through both barriers retains the remaining matrix/K-loop continuation |
| Dense shared tiles | All 16×32 A cells, including row-tail zeros, and 32×tileN B cells equal the dense input coordinates |
| Native matrix phase | All operand loads and all 8/16 MFMA instructions for one valid K32 iteration; all 256 results per instruction read the old snapshot, and the final C values equal the source-order two-pass result using original warp9/17 fuel |
| Complete execution | Every K32 iteration, actual K increment/back edge, guarded converted output stores, complete block and grid termination with the original fuel; global inputs preserved |
| Logical controls | Nine altered sources and five direct false Lean statements fail logically; four changed references and twenty rehashed certificate changes are refused |
| Stage controls | The full real reader rejects38 fully rehashed scope changes before extraction; historical grid components retain62 controls at their earlier scope |
| Finite complete execution | Four launches, 18,048 independent output expressions, 359,424 actual trace events; no conflicts, one output writer and unchanged inputs |
| Finite semantic controls | Wrong matrix operand, missing reuse barrier, missing staging barrier, shortened K loop, aliased output and missing half conversion are detected |
| Native compilation | Both tile paths disassemble to 8/16 native MFMA sites, wave64 and expected shared sizes |
| Paired numerical validation | 120 launches, 820,224 CPU float64 output comparisons; zero failures at `atol=rtol=0.002` |
| Host agreement | Zero FP16 bit differences between `mi350` and `mi350-2`; 380 total FP16-word differences against separately rounded CPU Torch FP32 |
| Memory preservation | Every input matrix and allocation guard unchanged; every output initialized to NaN before launch |
| Numerical controls | Ten fully rehashed false packets rejected, including a wrong output, missing final store, changed read-only input and false proof claims |
| Packaging | All83 required proof resources and SDK files match the wheel; installed verification/recheck outside the checkout pass and a rehashed changed statement is refused |

The numerical study covers ten `(M,K,N)` shapes:
`(1,32,64)`, `(15,32,128)`, `(16,64,192)`, `(17,32,64)`, `(17,32,128)`,
`(33,64,192)`, `(33,64,256)`, `(64,256,512)`, `(65,96,64)` and `(65,96,128)`.
The 64×256×512 shape matches the paper's general GEMM configuration; it does
not identify the authors' unavailable production AWQ configuration. Six input
families exercise seeded normal values, signed zero, structured dyadics,
row/K basis selection, half subnormals and cancellation.

The paired run requires three consecutive idle GPU samples and at least 98%
free memory before allocating inputs. Earlier immediate activity samples
stopped three MI350 attempts before any launch. One earlier 60-launch
MI350-2 packet preceded the stable-idle observer; it is recorded separately
and excluded from the paired 120-launch audit. Total hardware launches in
this study are 180. No model calls were made.

The shape contract requires positive dimensions, K divisible by 32, N divisible
by 64 and signed address bounds on the three matrix products. Source-derived
fuel remains lane512, warp9/17, block`2*(K/32)+1`, grid1. Every new Lean module
uses `maxRecDepth=10000` and `maxHeartbeats=2000000`. No proof option, machine
fuel or shape limit was raised to close these components.

The [complete real proof](REAL.md) records the current source-bound scope.
The [complete grid execution proof](GRID_EXECUTION.md) retains the preceding
execution-only checkpoint. Historical `source-components-v1` and its release
retain the earlier first-six-instruction result; `a-staging-v1` records the
later 256-audit result. `lane-staging-v1` records the earlier 363-audit result.
`block-staging-v1` records the earlier 418-audit result; `native-matrix-v1`
records the earlier 525-audit result; `whole-grid-v1` records the earlier
644-audit result. `canonical-real-v1` records the full 734-audit result.
The [complete grid execution archive](https://github.com/harsh-nod/lark/releases/tag/native-awq-whole-grid-20261112)
passes anonymous download, hash and Git-source binding checks.
The earlier [native matrix-phase archive](https://github.com/harsh-nod/lark/releases/tag/native-awq-matrix-phase-20261112)
retains its anonymous download, hash and Git-source binding checks. The earlier
[whole-block source archive](https://github.com/harsh-nod/lark/releases/tag/native-awq-block-staging-20261112)
and
[per-lane source archive](https://github.com/harsh-nod/lark/releases/tag/native-awq-lane-staging-20261112)
retains its anonymous download, hash and Git-source binding checks.
Evidence is under [results](results), with standalone
source and GPU archives in the
[original checkpoint release](https://github.com/harsh-nod/lark/releases/tag/native-awq-gemm-checkpoint-20261112).
The source replay rebuilds outside Git without an owned compiled cache. GPU
archives include frozen operands, exact kernel sources, raw outputs, compiler
commands, dependency hashes and captured compiler-input files. They establish
the reported numerical observations, not a hardware rounding theorem or the
paper's original model pass rates, token costs or NVIDIA latency results.

From the repository root:

```sh
python3 -m unittest discover -s tests -p test_native_awq_gemm.py -v
python3 reproduction/production_awq_gemm/run_symbolic.py --output /tmp/awq-finite
python3 reproduction/production_awq_gemm/check_components.py \
  --output /tmp/awq-components --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_awq_gemm/replay_components.py \
  --packet /tmp/awq-components --archive /tmp/awq-components/source-project.tar.gz \
  --output /tmp/awq-replay --lean-bin /path/to/lean-4.19.0/bin
```

Use `verify-native-awq-gemm` and generic `check` for complete source
certificates; [REAL.md](REAL.md) gives export, frozen replay, scope-control and
installed-package commands. Original adapted PTX/model/token/NVIDIA results
remain separate dependencies.
