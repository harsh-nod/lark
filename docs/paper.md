# Relationship to the paper

Primary source: [arXiv:2611.02028v1](https://arxiv.org/html/2611.02028v1),
read with particular attention to Sections 3–4 and Appendices A.7–A.13.
This is an independent implementation, not an upstream release.

The [MI350X extension](../reproduction/nonlinear/README.md) adds a second pinned
model with nonlinear scalar functions and explicit FP16 conversions. Its proofs
still use concrete reduced shapes and abstract operations; it does not reproduce
the paper's original programs or induction mechanism. IEEE rounding and formal
numerical-error bounds are outside both the paper's main theorem and our proofs.

The [pointwise induction extension](../reproduction/pointwise/README.md) now
proves a restatement of the existing nonlinear machine's grid fold by induction.
It certifies three full-length FP16 families, with one thread per block. This
scalable profile remains much narrower than general tiled/collective proofs.

The [counted-loop extension](../reproduction/reduction/README.md) proves a
serial dot-product loop and actual grid fold for full-size GEMV. The
[matrix](../reproduction/matrix/README.md) and [Linear](../reproduction/linear/README.md)
profiles add GEMM, BMM and bias epilogues. [RoPE](../reproduction/rotary/README.md)
adds output-parity branches and interleaved input pairing.
[Valid convolutions](../reproduction/convolution/README.md) add dense/depthwise
NCHW address proofs. These six induction profiles cover ten paper-size families
with independent scalar programs and
exact-source HIP checks on both MI350X hosts.

| Paper component | Implementation | Extent and differences |
| --- | --- | --- |
| Machine state, §4.1 | `lean/Lark/Model.lean`, `Nonlinear.lean` | Separate pinned profiles with thread PCs, index/scalar registers, scoped memories, geometry and access traces |
| Per-operation semantics, §4.1 | `execute`, `evalExpr`, `evalIndex` | Closed scalar operation sets; separate index/scalar types; nonlinear-v2 adds explicit FP16 storage conversions |
| Exact arithmetic | `Ops α` | Universally quantified operations support an exact real interpretation; no Mathlib or IEEE formalization |
| Hierarchical phase folds, Eq. 2 | `runLane`, `runWarp`, `runBlock`, `runGrid` | Warp, block, grid, halt cuts; separate fuel for each level; convergence checks |
| Race freedom, Obligation 1 | `raceFree`, `conflict`, `ordered` | All access pairs in a successful symbolic execution; scope-aware epoch ordering; checked again for arbitrary scalar inputs in the final theorem |
| Source translation and read-back | `lark_kernels/frontend.py` | Lossless token stream plus strict CUDA/HIP lowering; both parser and lowering remain trusted |
| Segmentation, Obligation 2 | `Segment`, `flatten`; induction libraries under `lean/Lark/` | Bounded profile checks syntactic grouping; separate profiles prove pointwise grid folds, counted GEMV/GEMM/BMM/Linear/convolution loops and RoPE branches by induction. No general loop/tile recovery |
| Tensor reference formalization | `lark_kernels/spec.py` | Independent PyTorch AST reader for a closed set of fixed-shape operations; does not execute reference code |
| Equivalence, Obligation 3 | `segment_equivalence` | Completion, race freedom, and output equality for every scalar interpretation, input, and outside-memory function |
| End-to-end assembly | `assemble`, `kernel_eq_spec`, `kernel_eq_spec_pre` | Immutable statements; reference-independent kernel lowering; satisfiable standard precondition |
| Agent–checker iteration | `lark_kernels/certificate.py` | Bounded local proof-provider protocol, diagnostics and immutable statements; deterministic default prover; optional HTTP model adapter |
| Certificate export, A.12 | `Main.lean`, task/source/reference, report | Dependency-free standalone Lean project, explicit axioms, source/model hashes, separate source-binding recheck |
| Mutation evaluation, §5.2 | Study runners under `reproduction/` | Independent reduced/full-length arithmetic mutants checked directly in Lean; GEMV changes fail fixed-program structural equality; not the original 42 mutants |
| Production softmax race | `reproduction/production_race.py` | Checked thread-0/thread-80 address conflict for the pinned upstream formula, plus a certified minimal repair; not a full production-kernel certificate |
| Hardware experiments | GPU study runners under `reproduction/` | MI300X/MI350X numerical checks/timings; reduced, full-size pointwise/GEMV/GEMM/BMM certified-source checks on both MI350X hosts; separate scalar and binary16 probes |

The [reproduction study](../reproduction/README.md) records exactly which experiments
were run. KernelCraft model pass rates/token costs, the original production-kernel
certificates, original kernel speedups, PTX/H100 experiments, induction/LLM ablations,
and complete per-opcode hardware sweeps remain unreproduced. Original artifacts were not present
in the arXiv source bundle; NVIDIA hardware is only one of the missing requirements.

The source frontend is intentionally smaller: no PTX, packed/vector arithmetic,
tensor-core fragment layouts, shuffles, cooperative grid-sync
templates, asynchronous instructions, arbitrary layouts, dynamic shapes,
in-place arguments, or general aliasing. The machine has a grid cut, but the
source frontend refuses grid synchronization until a host contract and pinned
hardware template are provided.

The paper uses unbounded memories and does not prove allocation bounds.
This profile checks accesses against finite declared buffer sizes, a stronger
condition within its narrower interface. This does not eliminate the need to
trust that the host allocates the declared buffers correctly.

The symbolic preflight checks expression structure, not algebraic equality.
The proposed segmentation retains flat branch targets and verifies grouping
by flattening. It is useful as a small proof-provider interface and a sound
certificate boundary, but it does not reproduce the paper's scalability from
induction over loop/tile restatements. The newer pointwise, GEMV and matrix profiles supply
checked induction theorems for narrow launch/program patterns. The [coverage ledger](../reproduction/COVERAGE.md)
tracks the remaining paper results separately from these independent studies.
