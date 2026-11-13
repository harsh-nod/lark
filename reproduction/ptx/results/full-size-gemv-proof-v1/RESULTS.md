# Exact-source full-size FP16 PTX GEMV proof

One independent 512×1024 FP16 matrix-vector program has a source-bound Lean
proof through a separate development checker. The actual NVRTC 12.9.86 PTX
8.8/sm_80 output contains 119 instructions. Matrix [512,1024], vector [1024,1],
output [512,1], all FP16 dtypes, grid 512, block one, warp 32 and the original
CUDA contract fuel [4102,1,1,1] remain unchanged.

The immutable Main binds the complete parsed instruction list and independently
closed reference AST. Lean checks the twelve-instruction prologue, all 64
sixteen-term iterations, actual pointer/counter/predicate/backward-branch control,
output store and ret. The complete-launch theorem covers all 512 active lanes,
race freedom of the actual recorded memory events, and every extracted output
against the ordered 1,024-term interpretation of `(a.float() @ b.float()).half()`.
Finite successful instruction transitions establish execution without a new fuel
or an assumed loop summary. CUDA fuel is data for its separate model.

Four retained positive Main checks passed: original SDK export, dedicated
outside-checkout/no-Git replay, the controls' fresh positive replay, and isolated
installed-wheel replay. Each rebuilds all four owned Lean modules from trusted
source, for 16 module builds, 102 library axiom audits and six Main audits per
check. Only propext, Classical.choice and Quot.sound occur. No old owned olean
cache is used. These are repeated checks of ONE independent development kernel.

Four accepted-grammar source mutations fail directly in Lean at source_program:
wrong product, wrong loop-counter stride, premature loop exit and conflicting
output address. None times out. They preserve all task/launch/fuel data. These
are source-binding controls, not general false-kernel classification or the
paper's original 42 mutants.

The wheel was built offline with setuptools 80.9.0 and wheel 0.45.1, installed
without dependencies, and replayed with Python isolated mode outside the checkout
and with Git absent from PATH. All source identities and the Main match. The
previous ReLU profile's owned-source bindings and regenerated Main also remain
byte-identical; that compatibility check adds no new ReLU proof or GPU trial.

The proof uses declared abstract scalar semantics. Parsing/reference
formalization, logical pointer provenance, scalar-operation correspondence and
aligned disjoint non-wrapping host allocations remain trusted. It establishes no
IEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or
conformance, original optimized kernel, original model result or paper table.
No new legacy SDK profile is registered, no model call or GPU experiment was
performed, and the six fixed-scaffold model cohorts remain unchanged. Other
full-size PTX families and original artifacts remain unfinished or unavailable.

Five deterministic archives preserve the actual export, replay, controls,
installed-wheel validation and wheel build. Each has a complete hash inventory
and was round-trip checked. Captured Python/Lean/oleans are data; replay checks
matched current trusted source, builds all four owned modules in one fresh import
root, and regenerates and checks the same Main. Resource limits remain
maxRecDepth 10000, maxHeartbeats 2000000, 180 seconds per Lean process and 600
seconds per source-import aggregate; legacy libraries retain their source limits.
See [the development checker commands](../../DOT.md).
