# Bounded scalar PTX extension

This adds a third source reader to the existing Lean machine. Four independent
tiny float32 PTX programs have source-bound certificates: copy with a full CTA
barrier, vector addition with a padded launch, ReLU, and a two-term GEMV.
These are not the paper's original PTX programs or Level-2 results.

The accepted subset is explicitly pinned to `.version 8.0`, `.target sm_80`,
64-bit addressing and one entry with named `.param .u64` buffer arguments.
Declarations, comments and whitespace are preserved in lossless token data.
Every token must belong to the closed grammar; unsupported instructions and
modifiers are refused. The reader and lowering remain trusted Python code.
Instruction forms follow NVIDIA's [PTX ISA reference](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).

Supported instructions are `ld.param.u64`, `mov.u32/u64/f32`, `add.u32/u64`,
`mul.lo.u32`, `mul.wide.u32`, integer `setp.{eq,ne,lt,le,gt,ge}.u32`,
forward `bra`/`@p bra`/`@!p bra`, `ld.global.f32`, `st.global.f32`,
`add/sub/mul.rn.f32`, `max.f32`, `bar.sync 0`, and one terminal `ret`.
Special thread/block registers are read through `mov.u32`. Static single
assignment, at most 256 registers/instructions, and the existing bounded launch
and buffer limits keep this deliberately small. Only exact finite hexadecimal
float literals are accepted; floating operations have abstract exact semantics.

Integer operations must stay in the nonnegative int32 range. Each pointer keeps
its named buffer and a runtime byte-offset register. Every float32 access has
a generated alignment guard before converting bytes to cell indices. If the
offset is misaligned the guard cannot complete; a successful Lean theorem
therefore checks alignment. Host parameter addresses must still designate the
declared aligned, disjoint allocations without 64-bit address wrap.

Pointer initialization and comparison predicates produce actual machine
assignments. Skipping a definition cannot silently create an initialized
pointer or predicate. The direct Lean controls include wrong arithmetic,
conflicting output stores, misaligned byte strides and a skipped predicate
definition. They bypass Python preflight and must fail in Lean without timeout.
These four controls are independent mutants, not the paper's original 42.

```bash
python3 -m lark_kernels verify reproduction/ptx/cases/vector_add/kernel.ptx \
  --reference reproduction/ptx/cases/vector_add/reference.py \
  --task reproduction/ptx/cases/vector_add/task.json \
  --output /tmp/ptx-vector-add --lean /path/to/lean-4.19.0/bin/lean
python3 -m lark_kernels check /tmp/ptx-vector-add \
  --lean /path/to/lean-4.19.0/bin/lean

python3 reproduction/ptx/run.py --output /tmp/ptx-study \
  --lean /path/to/lean-4.19.0/bin/lean
# Optional CPU-only NVIDIA assembly check; no NVIDIA GPU is needed:
# append --ptxas /path/to/ptxas
```

Certificates retain `kernel.ptx`, the independent reference, task, translation,
immutable Lean statement, proposal, logs and hash manifest. They use the existing
unmodified `Model.lean` and universal scalar `Correct` theorem. CUDA/HIP exports
retain their existing format.

There are no NVIDIA execution or timing results. Assembly checks establish that
the fixtures compile, not hardware conformance or correctness of generated SASS.
Tensor cores, shuffles, shared memory, general pointer arithmetic/aliasing,
register reassignment, loops, predicated memory, packed/vector operations,
atomics and async instructions remain unsupported. These certificates add
symbolic PTX coverage while the [original-paper ledger](../COVERAGE.md) remains
incomplete. [Recorded results](RESULTS.md).
