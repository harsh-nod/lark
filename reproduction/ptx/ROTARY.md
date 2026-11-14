# Full-size compiled interleaved RoPE development proof

The unchanged [compiler input](full-size/rope) has FP16 x/out[256,128] and
cosine/sine[256,64], grid 32,768, block 1, warp 32 and original CUDA fuel
`[8,1,1,1]`. The reference reshapes x into pairs, selects each coordinate,
multiplies by sine/cosine, subtracts or adds, interleaves with stack, reshapes
and finally converts to half. All source and contract bytes are preserved.

The complete source-bound abstract proof passed four fresh verification checks
with 32 fresh owned module builds and three positive rechecks. Four direct
Lean binding controls and 17 coherently rehashed recording controls passed.
The installed wheel replay ran with isolated Python outside Git and without
network access. These checks establish one independent development kernel.
Anonymous publication verification and the new source CI job remain pending.

The [evidence packet](results/full-size-rotary-proof-v1/RESULTS.md) preserves
every payload, all 17 pre-SDK development attempts (six passing partial checks,
eleven failures), preparation, and the failed wheel-build preflight. Failed
checks are never counted as accepted proofs. The entire installed environment
is data: file symlinks are archived as regular bytes and original link targets
are retained separately. No captured code or object file is executed by the
recorded-evidence reader.

The strict reader retains all 51 instructions and 52 declared physical
registers. [PtxRotary.lean](../../lean/Lark/PtxRotary.lean) models guarded
32-bit comparison, initialized predicates, predicate xor/not and unconditional
branches alongside the existing scalar instruction model. Instruction meaning
follows [NVIDIA PTX ISA 8.8](https://docs.nvidia.com/cuda/archive/12.9.1/parallel-thread-execution/index.html).
Seven reader tests cover source readback, task bounds, reference structure,
typed operand validation and constructor-injection refusal.

[PtxRotaryKernel.lean](../../lean/Lark/PtxRotaryKernel.lean) proves that each
valid lane executes its actual 41-instruction path through return, including
the five real memory accesses. One shared full-launch witness has the actual
source execution, race-free access trace, correct output and preservation
outside the output footprint for all 32,768 lanes and arbitrary abstract input
memory. The standard initial-memory precondition is proved satisfiable.

[PtxRotaryReference.lean](../../lean/Lark/PtxRotaryReference.lean) gives the
closed tensor expression an independent shape-checked denotation for reshape,
select, multiplication, subtraction, addition, stack and half conversion.
It does not execute PTX. Its denotation is linked to the kernel theorem.
Symbolic launch and extraction lemmas avoid expanding a concrete 32,768-element
term during kernel checking. All original shapes, launch and CUDA fuel remain
unchanged; finite PTX execution uses inductive successful transitions rather
than an added execution-fuel allowance.

Each fresh check compiles eight owned Lean modules from trusted source and
audits 265 library declarations plus seven generated proof declarations. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. SDK replay regenerates
the identical Main from captured inputs, matches all 64 owned source bindings
(56 Python, eight Lean), and never loads captured object files. The wheel uses
the same source bytes. No legacy registered profile is added.

For a fresh proof and source-only replay, with Lean 4.19.0:

```bash
python3 -m lark_kernels.ptx_rotary_certificate verify \
  --source reproduction/ptx/full-size/rope/kernel.ptx \
  --reference reproduction/ptx/full-size/rope/reference.py \
  --contract reproduction/ptx/full-size/rope/task.json \
  --output /tmp/lark-rotary-export --lean /path/to/lean-4.19.0/bin/lean

python3 -m lark_kernels.ptx_rotary_certificate replay \
  --recording /tmp/lark-rotary-export --output /tmp/lark-rotary-replay \
  --lean /path/to/lean-4.19.0/bin/lean
```

To validate the retained evidence without Lean, Git, models or GPUs:

```bash
python3 -I reproduction/paper_results/ptx_rotary_evidence.py \
  --packet reproduction/ptx/results/full-size-rotary-proof-v1 \
  --output /tmp/lark-rotary-recorded-evidence.json
```

Each Lean process keeps its 180-second cap, source imports their 600-second
aggregate cap, `maxRecDepth` 10,000 and `maxHeartbeats` 2,000,000. Earlier failed
drafts, including concrete-term recursion failures, are retained. No cap was
raised and no sorry, admit, native_decide or custom axiom was introduced.

Parsing, reference formalization, abstract scalar operations, ABI/pointer
correspondence and aligned disjoint non-wrapping allocations remain trusted.
There is no IEEE/error-bound, PyTorch or NVIDIA conformance, NVIDIA execution,
original optimized-kernel, model-pass-rate or full-paper reproduction claim.
