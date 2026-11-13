# Exact-source full-size FP16 PTX batched GEMM proof

One independent compiled BMM program now has a source-bound Lean proof for
A[32,64,256] times B[32,256,512], producing out[32,64,512], all FP16. The original
grid 1048576/block 1/warp 32 and CUDA fuel [1030,1,1,1] remain unchanged. The NVRTC
12.9.86 PTX 8.8/sm_80 program retains all 138 instructions and 149 declared registers.

Lean checks the 29-instruction prologue, actual 98-instruction body, five control
instructions and six-instruction epilogue. All sixteen actual loop iterations
compose from real source transitions through ret. The same whole-launch witness
covers all 1,048,576 lanes, race freedom over the actual recorded memory events,
every extracted output against the closed ordered 256-term reference AST, and
preservation of memory outside the output footprint. No loop summary is assumed.
The original CUDA fuel remains separate model data; PTX execution is an inductive
sequence of successful transitions and introduces no new execution fuel.

Four current-SDK positive Main checks passed: source export, fresh replay outside
Git with Git absent from PATH, the controls' fresh positive replay, and isolated
installed-wheel replay. Each builds all eight owned libraries from matched
trusted source: 32 fresh module builds, 271 library axiom audits and six Main audits
per check. Only propext, Classical.choice and Quot.sound occur. No old owned
compiled object is loaded. The final Main checks in about 1.7 seconds locally.

A genuine earlier SDK export also passed with eight fresh libraries and a
91.77-second Main check. It is preserved with its different renderer source pins.
The five retained official positive Main recordings are repeated checks of ONE
kernel: 40 successful fresh module builds and four positive rechecks. An actual
intermediate export failed at the unchanged maxRecDepth 10000 and is retained as
a failure. Selected cached development checks, including an unavailable-helper
failure and profiling, are separate history and count as no source-only export.
The SDK unit test passed fresh export/replay, one direct source refusal and ten
coherently rehashed tampering refusals. Its temporary Main files are not retained
positive recordings or extra independent kernels.

Four accepted-grammar mutations fail directly at source_program by decide:
product, loop-counter stride, B-pointer stride and shifted output address.
All four retain the shapes, launch, dtypes and fuel. None times out. These are
fixed-profile source-binding controls, not a general false-kernel classifier or
the original paper's 42 mutants.

The 0.3.0 wheel was built offline with setuptools 80.9.0 and wheel 0.45.1. Isolated
Python installed it without dependencies and replayed outside the checkout with
Git absent. All 60 owned source bytes match. Earlier ReLU source/Main bytes remain
identical. All 52 GEMV and 55 GEMM frozen source bindings and their Main bytes also
remain unchanged; their enlarged current rosters correctly refuse old recordings
before creating output. Their frozen 0.1/0.2 wheel hashes are unchanged. The initial
BMM renderer recording likewise requires its own exact source identity; no pin
is relaxed to accept the later renderer.

Python parsing/reference formalization, logical pointer provenance, aligned
disjoint non-wrapping allocations and scalar-operation correspondence remain
trusted. The proof uses declared abstract scalar semantics. It establishes no
IEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or
conformance, original optimized program, original model result or paper table.
No legacy SDK profile is registered. No model call or GPU trial was made.

Deterministic archives retain the complete official recordings, wheel build,
actual failed export, SDK test logs and selected development history. Every
member has a SHA256 inventory and a round-trip byte check. Captured Python,
Lean and compiled objects are data. Replay uses matched current trusted source
and fresh imports. Limits remain 180 seconds per Lean process, 600 seconds per
import aggregate, maxRecDepth 10000 and maxHeartbeats 2000000; legacy library
source limits are preserved. See [the checker commands](../../BATCHED.md).
