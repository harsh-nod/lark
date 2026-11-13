# Complete-source compiled FP16 batched GEMM

This development profile proves the unchanged compiled scalar BMM task:
`a[32,64,256] @ b[32,256,512] -> out[32,64,512]`, with FP16 buffers,
grid 1,048,576, block 1, warp 32 and original CUDA fuel `[1030,1,1,1]`.
The inputs are retained under [full-size/bmm](full-size/bmm).

The pure Lean theorem, complete source-bound export and matching fresh replay
have passed. The current export and replay each rebuild all eight owned modules;
the generated certificate checks in under two seconds on the recorded machine.
Four direct source controls and isolated installed-wheel validation also passed.
The [complete evidence packet](results/full-size-bmm-proof-v1/RESULTS.md) retains
all four current-SDK positive recordings, the earlier successful renderer,
the actual failed intermediate export and selected development history. Anonymous
publication and all twenty-two source CI jobs passed. This is one independent
development kernel, not an original optimized program or model-cohort result.

The [anonymous publication record](results/full-size-bmm-proof-publication-v1/results.json)
matched all 58 changed files (55,129,306 bytes) to source `6978f09`, with TLS
verification enabled. All nine archives, 702 archive members and 60 current
SDK/Lean source bindings were checked, including the wheel and earlier
renderer at its own source revision. Publication repeated no Lean, model or
GPU experiment.

The [actual source CI record](results/full-size-bmm-proof-ci-v1/results.json)
records all twenty-two jobs passing at source `6978f09`, including the
separate complete BMM cold export/replay, four direct source controls, SDK
adversarial tests and all existing checks. The later receipt commit changes
only this document and recorded receipts; all SDK, Lean, tests, workflow
and frozen snapshots retain their exact tested source identities.

A [bounded original-artifact observation](../paper_results/original-artifact-observation-bmm-20261113-v1/results.json)
still found the named KernelCraft repository empty and the abstract page
listing manuscript v1. It retains the initial anonymous-search rate limit
and a read-only authenticated fallback. These observations do not establish
global artifact absence or reproduce any scientific result.

The checked source has 138 static instructions and 149 declared registers. Its
29-instruction prologue computes the batch, local row and column addresses. The
98-instruction body performs sixteen ordered products and sums per iteration.
The five actual control instructions increment the input pointers and counter,
then branch from PC 131 to PC 29 until all 256 terms are consumed. Six epilogue
instructions store the result and return. The proof covers all sixteen actual
iterations and all 1,048,576 lanes, without reducing a shape or changing fuel.

`LarkPtxBatched.Bmm.Body.kernel_correct` combines actual source transitions,
whole-launch composition, race freedom over the actual recorded memory events,
extraction equal to the closed batched-matmul reference AST, and preservation
of memory outside the output allocation. The existential launch witnesses are
stopped machines reached by the actual program; no instruction or loop summary
is assumed. The CUDA fuel remains separate data for its original model. The PTX
proof uses finite inductive transition sequences and introduces no new fuel.

The declared abstract scalar interpretation, Python parsing/reference
formalization, logical pointer provenance, aligned disjoint non-wrapping
allocations and scalar-operation correspondence remain trusted. This establishes
no universal IEEE/error-bound theorem, PyTorch or NVIDIA backend conformance,
NVIDIA execution, original model pass rate, or full-paper reproduction.

The SDK entry points are separate from the legacy `lark verify/check` profiles:

```bash
python3 -m lark_kernels.ptx_batched_certificate verify \
  --source reproduction/ptx/full-size/bmm/kernel.ptx \
  --reference reproduction/ptx/full-size/bmm/reference.py \
  --contract reproduction/ptx/full-size/bmm/task.json \
  --output /tmp/lark-bmm-export --lean /path/to/lean-4.19.0/bin/lean

python3 -m lark_kernels.ptx_batched_certificate replay \
  --recording /tmp/lark-bmm-export --output /tmp/lark-bmm-replay \
  --lean /path/to/lean-4.19.0/bin/lean
```

Use fresh output directories. Export and replay build all eight owned modules
from source, then check the regenerated `Main.lean`. Each Lean process has a
180-second cap, with a 600-second aggregate import-build cap, `maxHeartbeats`
2,000,000 and `maxRecDepth` 10,000. Old owned compiled objects are not loaded.
Captured Python, Lean and compiled objects remain inventory-bound data; replay
uses the current installed trusted SDK and requires its exact source roster and
bytes to match the recording before producing output.

The eight libraries are `Nonlinear`, `Pointwise`, `PtxPointwise`, `PtxDot`,
`PtxMatrix`, `PtxBatched`, `PtxBatchedInit` and `PtxBatchedBody`. The wheel includes
their sources. Standard-axiom audits allow only `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `admit`, custom axiom or `native_decide` is accepted.

SDK 0.3 adds two Python files to the complete trusted source roster. Earlier
recordings retain their exact SDK and wheel identities; their source pins are
not relaxed to accept the enlarged roster. Use the matching frozen wheel for
an earlier recording, or create a fresh recording with the current SDK.
