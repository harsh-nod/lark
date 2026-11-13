# Exact-source full-size FP16 PTX GEMM proof

One independent 64×256 by 256×512 FP16 matrix-multiply program has a
source-bound Lean proof through a separate development checker. The exact
NVRTC 12.9.86 PTX 8.8/sm_80 source contains 171 instructions. All original
shapes and dtypes, grid 32768/block one/warp 32 and CUDA fuel [1030,1,1,1]
remain unchanged.

The complete parsed program and independently closed Python reference AST are
bound in the immutable Main. Lean checks the 47-instruction prologue, all sixteen
iterations of the real backward loop, pointer/counter/predicate control, output
store and ret. The complete-launch theorem covers all 32,768 active lanes, race
freedom of actual memory events, every extracted output against the ordered
256-term interpretation of `(a.float() @ b.float()).half()`, and preservation
outside the output footprint. Successful instruction transitions establish
execution without a new fuel or an assumed loop summary. CUDA fuel remains
separate model data.

Four retained positive Main checks passed: SDK export, dedicated outside-checkout
replay with Git absent from PATH, the controls' fresh positive replay, and an
isolated installed-wheel replay. Each compiles all five owned Lean modules from
matched trusted source: 20 fresh module builds, 169 library axiom audits and
six Main audits per check. Only propext, Classical.choice and Quot.sound occur.
No old owned olean cache is loaded. These are repeated checks of ONE kernel.

Four accepted-grammar changes fail directly in Lean at source_program: wrong
product, loop-counter stride, B pointer stride and conflicting output address.
None times out. All task/launch/fuel data remains unchanged. These are fixed
source-binding controls, not a general incorrect-kernel classifier or the
paper's original 42 mutants.

The 0.2.0 wheel was built offline with setuptools 80.9.0 and wheel 0.45.1,
installed without dependencies and replayed with isolated Python outside Git.
All 55 source bindings and the Main match. The prior ReLU profile's source pins
and Main remain identical. All 52 frozen GEMV source bindings and its Main also
remain unchanged, but its 0.1 recording correctly refuses the two additional SDK
modules before creating output. That frozen recording requires its recorded
0.1 wheel; no source pin was relaxed. A first installed-wheel probe expected the
later source-binding refusal rather than the earlier exact-roster refusal; its
failure is retained separately and is not counted as a replay.

Python parsing/reference formalization, logical pointer provenance, aligned
disjoint non-wrapping host allocations and scalar-operation correspondence remain
trusted. The proof uses declared abstract scalar semantics. It establishes no
IEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or
conformance, original optimized kernel, original model result or paper table.
No legacy SDK profile is registered, and no model call or GPU trial was made.
The six fixed-scaffold model cohorts remain unchanged. Broader full-size PTX
families and the original artifacts/experiments remain unfinished or unavailable.

Five deterministic archives preserve the actual export, replay, controls,
installed-wheel validation and wheel build, with complete member inventories and
round-trip checks. Captured Python/Lean/oleans are data. Replay uses matched
current trusted source and a fresh import root. Limits remain maxRecDepth 10000,
maxHeartbeats 2000000, 180 seconds per Lean process and 600 seconds per import
aggregate; legacy libraries retain their source limits.
See [the development checker commands](../../MATRIX.md).
