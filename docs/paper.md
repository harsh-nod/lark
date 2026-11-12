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
NCHW address proofs. [Normalization](../reproduction/normalization/README.md)
adds RMSNorm/LayerNorm/Softmax reduction phases. The
[two-launch FFN](../reproduction/feedforward/README.md) connects both certified
matrix products through the actual first final memory. [SwiGLU](../reproduction/swiglu/README.md) adds FP32 projections, a
checked SiLU/product grid and four-stage dataflow. These nine profiles cover
fifteen paper-size families (all twelve Level-1 families plus RoPE/FFN/SwiGLU) with
independent scalar programs and
exact-source HIP checks on both MI350X hosts. The
[dense attention profile](../reproduction/attention/README.md) connects three
launches for full-size dense SDPA and grouped-query attention, bringing the
independent full-size coverage to all seventeen families. It does not implement
FlashAttention's online algorithm.

| Paper component | Implementation | Extent and differences |
| --- | --- | --- |
| Machine state, §4.1 | `lean/Lark/Model.lean`, `Nonlinear.lean` | Separate pinned profiles with thread PCs, index/scalar registers, scoped memories, geometry and access traces |
| Per-operation semantics, §4.1 | `execute`, `evalExpr`, `evalIndex` | Closed scalar operation sets; separate index/scalar types; nonlinear-v2 adds explicit FP16 storage conversions |
| Register collectives | `Collective.lean`, `ShuffleTransfer.lean`, `lark_kernels/collective.py` | Opt-in full-wave64 HIP shuffle snapshots, four forms, no memory fence; five independent whole-launch certificates. No partial masks or tensor-core integration |
| Exact arithmetic | `Ops α`, optional `lean-real/` | Default proofs quantify over abstract operations; pinned Mathlib real interpretation and source-bound wave sum are optional; no IEEE theorem |
| Hierarchical phase folds, Eq. 2 | `runLane`, `runWarp`, `runBlock`, `runGrid` | Warp, block, grid, halt cuts; separate fuel for each level; convergence checks |
| Race freedom, Obligation 1 | `raceFree`, `conflict`, `ordered` | All access pairs in a successful symbolic execution; scope-aware epoch ordering; checked again for arbitrary scalar inputs in the final theorem |
| Source translation and read-back | `lark_kernels/frontend.py`, `ptx.py` | Lossless token stream plus strict CUDA/HIP and bounded scalar PTX lowering; parser and lowering remain trusted |
| Segmentation, Obligation 2 | `Segment`, `flatten`; induction libraries under `lean/Lark/` | Bounded profile checks syntactic grouping; separate profiles prove pointwise grid folds, counted GEMV/GEMM/BMM/Linear/convolution/normalization loops and RoPE branches by induction. No general loop/tile recovery |
| Tensor reference formalization | `lark_kernels/spec.py` | Independent PyTorch AST reader for a closed set of fixed-shape operations; does not execute reference code |
| Equivalence, Obligation 3 | `segment_equivalence` | Completion, race freedom, and output equality for every scalar interpretation, input, and outside-memory function |
| End-to-end assembly | `assemble`, `kernel_eq_spec`, `kernel_eq_spec_pre` | Immutable statements; reference-independent kernel lowering; satisfiable standard precondition |
| Agent–checker iteration | `lark_kernels/certificate.py` | Bounded local proof-provider protocol, diagnostics and immutable statements; deterministic default prover; optional HTTP model adapter |
| Certificate export, A.12 | `Main.lean`, task/source/reference, report | Dependency-free standalone Lean project, explicit axioms, source/model hashes, separate source-binding recheck |
| Mutation evaluation, §5.2 | Study runners under `reproduction/` | Independent reduced/full-length arithmetic mutants checked directly in Lean; GEMV changes fail fixed-program structural equality; not the original 42 mutants |
| Production softmax race | `reproduction/production_race.py`, `reproduction/production_softmax/` | Early minimal witness plus complete native source binding, initialized actual-trace conflict, racy complete one-row launch, and repaired whole-grid execution/race freedom/dense-real correctness; the development reader issues no registered softmax source certificate |
| Hardware experiments | GPU study runners under `reproduction/` | MI300X/MI350X numerical checks/timings; reduced and all seventeen full-size families with certified-source HIP checks on both MI350X hosts; separate scalar, binary16 and collective probes. PTX has assembly checks only |

The [reproduction study](../reproduction/README.md) records exactly which experiments
were run. KernelCraft model pass rates/token costs, the original production-kernel
certificates, original kernel speedups, PTX/H100 experiments, induction/LLM ablations,
and complete per-opcode hardware sweeps remain unreproduced. Original artifacts were not present
in the arXiv source bundle; NVIDIA hardware is only one of the missing requirements.

The [PTX reader](../reproduction/ptx/README.md) covers four independent tiny
float32 programs, not the original optimized kernels or NVIDIA execution.
The source frontends remain smaller: general packed/vector arithmetic beyond
the fixed native profiles, other matrix-instruction layouts, masked/partial-wave
shuffles, cooperative grid-sync templates, asynchronous instructions, arbitrary
layouts, dynamic shapes, and general aliasing/in-place interfaces beyond the
fixed seeded-buffer profiles remain unsupported. The machine has a grid cut, but the
source frontend refuses grid synchronization until a host contract and pinned
hardware template are provided.

The separate [full-wave shuffle profile](../reproduction/shuffle/README.md)
adds register-snapshot semantics for four HIP shuffle forms. A reusable Lean
phase proof certifies five complete 64-lane transport kernels; exact-source
bit-copy checks passed on both MI350X hosts. Shuffles preserve memory-order
epochs. That shuffle profile excludes tensor-core instructions.

The [native MFMA profile](../reproduction/mfma/README.md) separately models one
full-wave64 f32_16x16x16f16 instruction with default modifiers. Its complete
load/matrix/store program has a whole-launch certificate and exact-source
hardware checks on both hosts. It does not combine shuffles with MFMA, certify
the original production kernels or establish IEEE accumulation semantics.

The [multiwave scalar SiLU profile](../reproduction/production_silu/README.md)
proves a generic simulation of the unchanged lane/warp/block/grid folds and
discharges its lane and invariant contracts for the public upstream-style
scalar strided loop. It retains native blocks of up to 1,024 threads, handles
partial final waves and unequal iteration counts, and proves the independent
closed-reference expression for every output. Eight HIP/CUDA certificates were
rechecked, including two symbolic-only billion-cell extremes; three smaller
device-test shapes passed exact-source/upstream comparisons on both hosts.
This is one independently adapted function family, not the authors' original
production registry or packed vector fast path.

The optional [exact-real interpretation](../lean-real/README.md) constructs the
nonlinear operations over Mathlib's reals, proves canonical SiLU/dot reference
equalities and supplies reduction-tree/permutation and chunking lemmas. It
removes the need to assume algebraic laws for unrestricted operations. This is
mathematical preparation for optimized reductions; it does not add a new
optimized program or reproduce an original model/hardware experiment.

The [full-wave reduction extension](../reproduction/wave_reduction/README.md)
combines that algebra with actual execution, footprint and race-freedom proofs
for one independent native wave64 XOR butterfly. Its source-bound theorem
equates every output to an independent canonical real sum. Both AMD hosts match
the source addition tree bit for bit; fixed cancellation probes disagree with
CPU Torch and are reported separately. Original production reductions and
NVIDIA results remain unavailable.

The [native online-attention study](../reproduction/online_attention/README.md)
now proves the complete initialized launch, actual-trace race freedom and every
output's equality to dense exact-real SDPA for all supported group counts
1..65535 at N128/D256. All four key tiles, nine block phases and eight barrier
resumptions remain. Four source-bound canonical-real exports and independent
source-only replays pass. Half casts are identities in this real interpretation;
the source-ordered theorem retains explicit conversions. Paired AMD numerical
checks and the earlier algebra-only checkpoint remain separate evidence.

The current [production inventory](../reproduction/COVERAGE.md) has nine
independently adapted accepted families: SiLU-and-mul, weighted RMSNorm,
seeded in-place fused add RMSNorm, online attention, both native RoPE layouts,
both fused QK/RoPE layouts, distinct FlashInfer RMSNorm, guarded packed SGLang
RMSNorm, and native FP16 single-split-K AWQ GEMM. Their separate fixed profiles
publish 48 exports, with actual whole-launch correctness/race freedom and
source/reference bindings. The RMSNorm, attention, fused QK/RoPE and AWQ real
profiles additionally connect to independent dense mathematical references.

The [AWQ proof](../reproduction/production_awq_gemm/REAL.md) composes actual
native MFMA operand snapshots through both K16 passes and every K32 tile,
retaining padded shared staging, block barriers, row guards, half conversion
and original source-derived fuel. Its four source instances replay 734 audits
over 83 owned modules and reject 14 false Lean claims. The distinct FlashInfer
and SGLang profiles retain logical32 reductions inside physical wave64; the
SGLang lane-zero shared-store repair and original unguarded conflict are explicit.
These are independent adaptations, not the authors' unavailable original
production sources, certificates, model outcomes or NVIDIA measurements.

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
