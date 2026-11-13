# Exact-source full-size FP16 PTX ReLU proof

One independent 16,384-element FP16 ReLU program now has a source-bound Lean
proof through a separate finite PTX checker. It parses the actual 15-instruction
PTX 8.8/sm_80 compiler output from the CPU assembly study. Input source,
reference, task, shape, dtype, grid (16,384), block (one thread), warp (32),
and original CUDA contract fuel [4,1,1,1] are unchanged. The structurally finite
PTX interpreter executes all 15 instructions; CUDA fuel is a separate model's
contract data and does not limit this PTX interpreter to four instructions.

The immutable Main binds the actual parsed instruction list and closed reference
AST in Lean, then proves whole-launch completion, race freedom for actual memory
events, segment equivalence and every reference output. Source-language PTX and
reference-contract-language CUDA are recorded separately. There is no captured
proof proposal or model call in this study.

The original export and three rechecks (dedicated source-only replay, controls'
positive replay, and an isolated installed-wheel replay) all passed. Each builds
three owned Lean modules from trusted source, for 12 module builds and four
positive Main checks total. These are repeated checks of ONE kernel. Each Main
has six axiom audits and the PTX library has 22. All use only the standard Lean
axioms propext, Classical.choice and Quot.sound. No old owned olean cache is used.

Four source mutations pass the reader and fail directly in Lean at the fixed
profile's source-program equality proof: wrong arithmetic, misaligned byte
stride, wrong output address and skipped half conversion. None times out. These
check source binding; they are not a general kernel-falsity classifier or the
paper's original 42 mutants.

The wheel was built using an isolated compatible backend (setuptools 80.9.0,
wheel 0.45.1), installed offline without dependencies into a fresh venv, then
replayed with Python isolated mode outside the checkout. Its source bindings and
Main match the export. The first build's incompatible system-backend failure is
retained separately; no project license or proof limit was changed to bypass it.

All floating operations have the declared abstract scalar semantics. The reader,
reference formalization, scalar-operation/ABI correspondence and aligned,
disjoint, non-wrapping host allocation assumptions remain trusted. This does not
establish IEEE/error-bound equivalence, NVIDIA execution/conformance, an original
optimized kernel, or an original model/table result. The separate development
checker registers no new legacy SDK certificate profile. Existing HIP/CUDA model
cohort results are unchanged. Other full-size PTX families remain unfinished.

`export.tar.gz`, `replay.tar.gz`, `controls.tar.gz`, `installed-wheel.tar.gz` and
`wheel-build.tar.gz` preserve exact source/contract/reference bytes, immutable
Main, translations, source identities, module sources, captured oleans, logs,
toolchain/axiom/resource checks, mutation inputs and installed-wheel receipts.
Each archive has a complete file/hash inventory and was round-trip checked.
Captured Python, Lean and oleans are data during source-only replay; trusted
current source is checked and compiled afresh. See ../../POINTWISE.md for commands.
