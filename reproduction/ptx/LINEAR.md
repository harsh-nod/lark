# Full-size compiled Linear development proof

The unchanged compiler input is retained in [full-size/linear](full-size/linear):
`a[64,256] @ b[256,512] + bias[512] -> out[64,512]`, with FP16 buffers,
grid 32,768, block 1, warp 32 and original CUDA fuel `[1030,1,1,1]`.
The reference converts all three inputs to float, performs the matrix product,
adds bias, then converts the result to half. Its cast order is preserved.

This is an incomplete development study. Four complete independent PTX kernel
proofs remain published; this work adds no completed kernel or model success.
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

The four one-fragment controls change a product, conversion source register,
bias shift amount or bias operation. Each is accepted by the grammar and
rejected at the generated exact-source equality, without timing out. They test
binding to this fixed development program; they do not establish correctness
of the unfinished bias epilogue, form a general kernel verifier or reproduce
the paper's original mutation experiment.

The earlier failed development checks and the first cold driver's audit-name
failure remain retained under their original versioned local directories.
The failed cold run is not accepted: the corrected driver qualified existing
theorem names, then completed the fresh seven-module check. No proof statement,
shape, fuel, heartbeat, recursion, process or aggregate limit was weakened.
The later driver ownership guard prevents an existing recording from being
overwritten during exception capture; it changes no Lean proof or input bytes.

## Remaining work

The actual bias-reading/addition epilogue, output store, return, whole-launch
composition, reference AST extraction, preservation outside the output and
actual access-trace race proof are required. A complete profile must receive
fresh source export/replay, adversarial and installed-package checks, retained
raw evidence, anonymous publication verification and actual source CI before
promotion. No SDK certificate or registered legacy profile exists for Linear.

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
