# Counted-loop GEMV induction

This independent extension proves the paper-size FP16 GEMV shape
`[512,1024] @ [1024,1] -> [512,1]` for HIP and CUDA source profiles.
[Results](RESULTS.md), [standalone HIP certificate](results/gemv-certificate/),
[paper coverage](../COVERAGE.md).

The launch uses **one scalar thread per row**, one block per output. These are
independent programs, with a serial FP32 accumulator, rather than the authors'
optimized kernels. Only HIP ran on hardware; CUDA certificates use CPU Lean.

The [proof library](../../lean/Lark/Reduction.lean) establishes the actual
`LarkNonlinear.Correct`, without changing the machine. A counted-loop invariant
covers each multiply-accumulate, branch, index update and jump. A grid-prefix
invariant establishes completion, every output, input preservation and trace
ownership/race freedom. The independent reference is a `List.range K` fold over
promoted products, mapped over rows. The theorem quantifies over M, K, every
operation interpretation, input and arbitrary outside memory. Signed 32-bit
address/index bounds are checked within the proof.

`verify-gemv` accepts only the nine-instruction program profile, positive FP16
shapes `[M,K]`, `[K,1]`, `[M,1]`, `M*K < 2^31`, native warp width, one thread/block
and fuel `[4*K+6,1,1,1]`. The closed reference AST is exactly
`(a.float() @ b.float()).half()` with validated imports, argument binding and
signature. It excludes shape-dependent branches, indexing, gathers and views.
The original bounded verifier retains its existing limits.

Exports contain all three proof/machine sources inline. `lark check` regenerates
the statement from fixed source/reference/task bytes, checks model and file
hashes, and reruns Lean with six final axiom audits. Only `propext`,
`Classical.choice` and `Quot.sound` occur in the final proofs. Arithmetic and half
conversions are abstract; this is not an IEEE/error-bound theorem. Source
lowering, the closed reference formalizer, host buffers/launch, and the external
connection between race-free phases and GPU interleavings remain trusted.

## Reproduce

Use Lean **4.19.0** and Python 3.11 or newer, at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-gemv reproduction/reduction/cases/hip/kernel.hip \
  --reference reproduction/reduction/cases/hip/reference.py \
  --task reproduction/reduction/cases/hip/task.json --output /tmp/lark-gemv
python -m lark_kernels check /tmp/lark-gemv
cd /tmp/lark-gemv
lean Main.lean
```

For the CPU/scaling study and prepared GPU inputs (the latter needs CPU PyTorch):

```bash
python reproduction/reduction/run_cpu.py --lean "$LARK_LEAN" \
  --output /tmp/lark-gemv-cpu
python reproduction/reduction/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-gemv-cpu --output /tmp/lark-gemv-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/reduction/run_gpu.py \
  --input /tmp/lark-gemv-input --output /tmp/lark-gemv-device
python reproduction/reduction/summarize.py
```

The GPU runner uses standard-library Python, HIP compiler/headers/runtime and
the repository's `reproduction` modules. It checks source/reference/task hashes
against the CPU certificate index and reconstructs the wrapper before compiling.
Each allocation has 128-byte guards, and both inputs are checked byte-for-byte
after every launch. Guards check writes; access safety is established separately
in the modeled Lean proof. GPU hosts do not rerun Lean.

The three mutation checks deliberately bypass the structural profile screen
and render changed actual IR against the fixed proved program/reference. Lean
rejects their structural-equality obligations. This is not a semantic diagnosis,
an original paper mutant, or evidence for the original rejection-channel counts.

The CPU archive contains successful proofs, independent recheck logs and failed
changed programs. Its source snapshot preserves the exact loaded runner and
libraries before later metadata-integrity hardening; regenerated statements
are checked byte-for-byte. The device source bundle preserves the runner,
wrapper validator, prepared values and index used by both hosts. Receipts bind
those files and the compiled library. Scaling uses one attempt per shape, and
only 512×1024 was allocated/executed on hardware.
