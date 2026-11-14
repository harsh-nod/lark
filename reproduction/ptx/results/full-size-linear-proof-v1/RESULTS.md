# Exact-source full-size FP16 PTX Linear proof

One independent original compiled matrix-plus-bias program has a source-bound
Lean proof for a[64,256] times b[256,512] plus bias[512], producing out[64,512],
all FP16. The original grid32768/block1/warp32 and CUDA fuel[1030,1,1,1] remain
unchanged. All179 instructions and189 declared registers are retained.

The same actual source witness executes the50instruction prologue, all16 real
113instruction matrix body iterations with five controls each, and all11 bias,
store and return instructions. Bias is added before the final half conversion.
All32768lanes, actual memory-event race freedom, closed reference AST extraction
and preservation outside output are covered. No instruction/loop summary or new
PTX execution fuel is assumed; original CUDA fuel remains separate model data.

Four complete SDK positive Main recordings check ONE kernel: source export,
no-Git fresh replay, the controls' fresh replay and isolated installed-wheel
replay. Each rebuilds ten owned source modules:40fresh builds in total, with
280library and sixMain axiom audits per check. Only propext, Classical.choice
and Quot.sound occur. Captured Python/Lean/compiled objects are data; trusted
matching source regenerates Main and builds every owned import freshly.

Four accepted-grammar one-fragment mutations reach the actual source_program
Lean equality and fail without timeout: product, signed-conversion source,
bias shift and bias operation. They preserve every shape/dtype/launch/fuel.
They test fixed-profile binding, not general kernel falsity or the original42
paper mutants. The full SDK integration test additionally passed fresh10export,
fresh10replay, direct wrong-product refusal and ten coherently rehashed attacks.
Its temporary Main files are not retained positive recordings or new kernels.

All12 pre-SDK development attempts are retained separately, including five
failures and seven accepted partial or library checks. They are not official
complete source-only SDK exports. Failed compiler recovery logs with sorryAx
were never accepted. The failed first cold driver retains its original partial
running label, with actual observed terminal1 recorded in history. No proof
statement, shape, fuel or resource cap was weakened. No failed official SDK
export occurred in this study.

The0.4.0wheel was built offline with setuptools80.9.0/wheel0.45.1, then installed
and replayed in isolated Python outside Git and the checkout with Git absent
from PATH. All64 trusted source bytes match. Original ReLU/GEMV/GEMM/BMM source
and Main bytes and frozen0.1/0.2/0.3wheels remain unchanged. Enlarged current
rosters refuse earlier recordings before output; exact old source pins remain
required. No legacy profile or model success is registered.

The abstract scalar correspondence, Python parsing/reference formalization,
logical pointer provenance and aligned disjoint non-wrapping allocations remain
trusted. This establishes no IEEE/error bound, PyTorch or NVIDIA conformance,
NVIDIA execution, original optimized program, original model result or full
paper reproduction. No model or GPU trial was performed for this proof study.

Seven deterministic archives retain all official recordings, installed package
validation, wheel, SDK test logs and complete retained development history.
Every member has a SHA256 inventory and a round-trip check. Limits remain180s
per Lean process,600s per source-import aggregate, maxRecDepth10000 and
maxHeartbeats2000000; legacy source limits are unchanged. Publication/actual CI
are separately gated. See [the checker commands](../../LINEAR.md).
