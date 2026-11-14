# Full-size compiled Linear development proof

The unchanged compiler input is retained in [full-size/linear](full-size/linear):
`a[64,256] @ b[256,512] + bias[512] -> out[64,512]`, with FP16 buffers,
grid 32,768, block 1, warp 32 and original CUDA fuel `[1030,1,1,1]`.
The reference converts all three inputs to float, performs the matrix product,
adds bias, then converts the result to half. Its cast order is preserved.

The pure complete-source theorem, fresh SDK source export/replay, four direct
source-binding controls, SDK adversarial test and isolated installed-wheel
replay have passed. The [complete evidence packet](results/full-size-linear-proof-v1/RESULTS.md),
anonymous publication verification and all twenty-three actual source CI
jobs passed. This fifth independent compiled PTX development proof adds
no original model success.
The original shapes, input bytes, launch geometry and CUDA fuel are unchanged.
The CUDA fuel remains separate data; actual PTX execution uses finite inductive
sequences of successful source transitions and introduces no new execution fuel.

## Checked milestones

- The strict reader retains all 179 instructions and 189 declared registers,
  including signed `cvt.s64.s32` at PC 43 and `shl.b64` at PC 169. Six reader
  tests pass. Source readback preserves every original byte.
- The extended abstract machine models sign extension of guarded signed32
  values and logical 64-bit left shift with zero fill, overflow truncation,
  unsigned32 shift amounts clamped to 64, and signed reinterpretation of the
  result. General result-range and bounded bias-column lemmas are proved,
  alongside checked negative, sign-bit and clamped-shift examples. The source
  is [PtxLinear.lean](../../lean/Lark/PtxLinear.lean); the instruction basis is
  [NVIDIA PTX ISA 8.8, sections 9.7.8.8 and 9.7.9.21](https://docs.nvidia.com/cuda/archive/12.9.0/parallel-thread-execution/index.html).
- The actual 50-instruction prologue is proved for every original active lane.
  Its final witness retains input/output/bias pointers, the saved bias column,
  all 16 B strides, A row offset, zero counter and zero accumulator. The source
  is [PtxLinearInit.lean](../../lean/Lark/PtxLinearInit.lean).
- A complete initialization check rebuilt all seven owned modules from source:
  57.4546 seconds for imports, 65.2430 seconds for the whole check, 222 library
  and four generated-proof axiom audits accepted, and four source-binding
  controls rejected. The raw output is retained locally at
  `/tmp/lark-ptx-linear-initialization-cold-v2-20261113`, produced at `835b278`.
  It is a prologue check; it establishes no complete kernel certificate.
- The actual 113-instruction body and all five loop controls are proved through
  all 16 real iterations, consuming all 256 terms and reaching PC 168. This
  composes with the actual prologue for arbitrary initialized inputs and every
  original lane. The saved bias column and bias/output pointers are preserved.
  [PtxLinearBody.lean](../../lean/Lark/PtxLinearBody.lean) passed with seven
  inventory- and source-bound cached imports and one fresh module build;
  its raw development output is retained locally at
  `/tmp/lark-ptx-linear-loop-v1-20261113` (10.1781 seconds, 28 library and two
  generated-proof axiom audits). This is not a cold complete-kernel export.
- The complete 11-instruction bias epilogue, output store and return passed
  in `PtxLinearExit.lean`: every original lane stops at PC 179 and changes only
  its own output. The same witness performs all 179 actual source instructions,
  including the real loop, and adds the bias before the final half conversion.
  The local development record `/tmp/lark-ptx-linear-exit-v1-20261113` retains
  eight verified cached imports, one fresh module, 12 library plus two generated
  axiom audits and the actual 4.3339-second check.
- `PtxLinearLaunch.lean` composes the complete 32,768-lane source launch and
  proves closed matrix-plus-bias reference extraction, actual access-trace race
  freedom and preservation outside the output for one shared launch witness.
  `/tmp/lark-ptx-linear-launch-v1-20261113` retains nine verified cached imports,
  one fresh module, 18 library plus six generated-proof axiom audits and the
  actual 4.2616-second development check. Full fresh export/replay is next.

The four one-fragment controls change a product, conversion source register,
bias shift amount or bias operation. Each is accepted by the grammar and
rejected at the generated exact-source equality, without timing out. They test
binding to this fixed development program. They do not form a general kernel
verifier or reproduce the paper's original mutation experiment.

The earlier failed development checks and the first cold driver's audit-name
failure remain retained under their original versioned local directories.
The failed cold run is not accepted: the corrected driver qualified existing
theorem names, then completed the fresh seven-module check. No proof statement,
shape, fuel, heartbeat, recursion, process or aggregate limit was weakened.
The later driver ownership guard prevents an existing recording from being
overwritten during exception capture; it changes no Lean proof or input bytes.

## Remaining work

The [anonymous publication record](results/full-size-linear-proof-publication-v1/results.json)
matched all 56 changed files (94,911,615 bytes), seven archives, 960 members
and 64 SDK/Lean source bindings to source `1e00541`, with TLS verification
enabled. It retained every development attempt, including all five failures.
The [actual source CI record](results/full-size-linear-proof-ci-v1/results.json)
records all twenty-three jobs passing, including the separate complete
Linear cold export/replay, four controls and SDK adversarial checks.
The later receipt commit changes only recorded receipts and this document
and the root README. All SDK, Lean, tests, workflow and frozen snapshots
retain their exact tested source identities. Publication repeated no
scientific proof, model or GPU trial. No registered legacy profile or
original model result is added.

The new SDK 0.4.0 profile `source-bound-compiled-linear-fp16-v1` has ten owned
Lean modules and 64 trusted source bindings (54 Python, ten Lean). The first
fresh export rebuilt all ten in 71.1261 seconds and checked Main in 2.9220
seconds. Dedicated no-Git source replay, the controls' fresh positive replay
and isolated installed-wheel replay all passed with identical regenerated Main.
These are four retained checks of one independent kernel, with 40 fresh module
builds and three positive rechecks. Earlier cached development checks and the
initialization-only cold study remain separate history.

The SDK integration test passed in 156.2493 seconds: fresh ten-module export,
fresh ten-module replay, direct product-source refusal and ten coherently
rehashed recording/proof/roster/axiom/claim refusals. Its temporary Main files
are not retained positive recordings. All earlier frozen wheel hashes and
source/Main identities remain unchanged. Enlarged current rosters correctly
refuse earlier GEMV, GEMM and BMM recordings before creating output; use their
matching original frozen SDK wheels.

```bash
python3 -m lark_kernels.ptx_linear_certificate verify \
  --source reproduction/ptx/full-size/linear/kernel.ptx \
  --reference reproduction/ptx/full-size/linear/reference.py \
  --contract reproduction/ptx/full-size/linear/task.json \
  --output /tmp/lark-linear-export --lean /path/to/lean-4.19.0/bin/lean

python3 -m lark_kernels.ptx_linear_certificate replay \
  --recording /tmp/lark-linear-export --output /tmp/lark-linear-replay \
  --lean /path/to/lean-4.19.0/bin/lean
```

For a fresh initialization-only check:

```bash
python3 reproduction/ptx/check_linear_initialization.py \
  --output /tmp/lark-linear-initialization-new \
  --lean /path/to/lean-4.19.0/bin/lean
```

Each Lean process retains its 180-second cap, the source-import aggregate its
600-second cap, `maxRecDepth` 10,000 and `maxHeartbeats` 2,000,000. Only the
standard axioms `propext`, `Classical.choice` and `Quot.sound` are allowed.
Parsing, reference formalization, abstract scalar operations, logical pointer
provenance and aligned disjoint non-wrapping allocations remain trusted.
This work establishes no IEEE/error bound, PyTorch or NVIDIA conformance,
NVIDIA execution, original model pass rate or full-paper reproduction.
