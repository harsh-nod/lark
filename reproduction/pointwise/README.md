# Inductive full-length pointwise certificates

This independent extension proves FP16 ReLU, SiLU and tanh-approximate GELU at
the paper's vector length **16,384**, for HIP and CUDA source profiles. It uses
the existing `LarkNonlinear.runLaunch`, `Correct`, `raceFree`, `initial` and
`extract` definitions. The machine and its existing certificates are unchanged.
[Results](RESULTS.md), [raw evidence](results/), [standalone GELU certificate](results/gelu-certificate/).

The launch has **one thread per block**, one block per output element. These
are independent programs, not the paper's optimized kernels or launch geometry.
Only HIP is executed on hardware; CUDA certificates are CPU Lean checks.

## Proof and trust boundary

The [induction library](../../lean/Lark/Pointwise.lean) proves a generic theorem
over length, scalar expression, operation interpretation, every input and
arbitrary outside memory. A lane executes the actual four machine instructions:
set its index from `blockIdx.x`, promote the input from half, evaluate and store
a half, then halt. A prefix invariant and grid-fold induction prove completion
and every output value. An ownership argument proves the actual `raceFree`
predicate; a generic extractor lemma covers all output cells.

The conclusion is the existing machine's `Correct`. Equality between the launch
and its inductive restatement is proved in Lean. Standalone exports include both
the machine and induction proof source; no cached local proof library is needed.

`verify-pointwise` accepts only this four-instruction profile, two equal 1-D FP16
buffers, length 1 through 2^31-1, the one-thread launch and fuel `[4,1,1,1]`.
The reference reader excludes indexing, reshaping, reductions, loops, conditions
and dimension-dependent expressions before lifting a scalar expression over the
array. Source and reference bodies are emitted separately. Lean checks their
agreement; no Python expression-equality or numerical screen rejects arithmetic
mutants first. The old bounded `verify` command retains its capacity limits.

`lark check` regenerates the statement from source/reference/signature, checks
both pinned library hashes, and reruns Lean with six final axiom audits.
Final proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Half and nonlinear operations remain abstract. No IEEE or error-bound theorem
is claimed. Source lowering, the closed elementwise reference formalization,
hardware correspondence, the host interface and the reduction from race-free
phases to GPU interleavings remain trusted.

## Reproduce

Use Lean **4.19.0**, Python 3.11 or newer, and the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-pointwise \
  reproduction/pointwise/cases/hip/gelu/kernel.hip \
  --reference reproduction/pointwise/cases/hip/gelu/reference.py \
  --task reproduction/pointwise/cases/hip/gelu/task.json \
  --output /tmp/lark-gelu-induction
python -m lark_kernels check /tmp/lark-gelu-induction
cd /tmp/lark-gelu-induction
lean Main.lean
```

The committed fixtures come from `make_cases.py`, which requires fresh destinations.
For the CPU study and prepared hardware inputs (the latter needs CPU PyTorch):

```bash
python reproduction/pointwise/run_cpu.py --lean "$LARK_LEAN" \
  --output /tmp/lark-pointwise-cpu --flat-timeout 30
python reproduction/pointwise/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-pointwise-cpu --output /tmp/lark-pointwise-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/pointwise/run_gpu.py \
  --input /tmp/lark-pointwise-input --output /tmp/lark-pointwise-device
```

The GPU runner needs standard-library Python, HIP compiler/headers/runtime, the
repository's `reproduction` modules and the prepared directory. It checks hashes
against the CPU certificate index and reconstructs the wrapper before compiling
the exact source. Six random trials and four probes check every output, unchanged
input bytes, and 128-byte guards before/after each allocation. Guards detect
writes; they do not prove absence of out-of-bounds reads. CPU Lean certificates
establish modeled access safety separately. GPU hosts do not rerun Lean.

## Evidence

`cpu-artifacts.tar.gz` contains successful proofs, failed arithmetic mutants and
flat timeouts. `cpu-source-snapshot.tar.gz` preserves the exact loaded source,
before formatting and stricter JSON-type guards; its runner hash matches `cpu.json`. Current
statements are checked against the archive. The device bundle contains the actual
runner, wrapper validator, source/reference/task text, prepared values and index
used on both hosts; device receipts hash those files and the compiled library.

Scaling uses one attempt per configuration and a 30-second flat-check limit.
Timings include Python and fresh Lean elaboration; other validation ran
concurrently. This is an independent experiment, not the original LLM ablation.
The largest lengths are proved without allocating or executing their arrays;
only length 16,384 is validated on hardware. The [coverage ledger](../COVERAGE.md)
records the broader unreproduced results.
