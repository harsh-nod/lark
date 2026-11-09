# Full-size interleaved RoPE induction

This independent extension certifies FP16 interleaved rotary pairs at the paper's
`[256,128]` shape, with `[256,64]` cosine/sine inputs. HIP and CUDA have separate
source-bound certificates. [Results](RESULTS.md), [evidence](results/),
[paper coverage](../COVERAGE.md).

One scalar thread/block computes each output, using its parity to choose the
real or imaginary formula. Each adjacent pair shares input/coefficient reads;
each thread writes its own output. This differs from the authors' optimized
program/launch. HIP runs on both MI350X hosts; CUDA is checked by CPU Lean.

## Proof boundary

The [Rotary library](../../lean/Lark/Rotary.lean) proves the actual unchanged
`LarkNonlinear.runLaunch` and `Correct`: completion, race freedom and all outputs,
for all inputs and arbitrary outside memory, under any scalar-operation
interpretation. The lane proof checks division/remainder, pair bounds, the branch
and both stores. A prefix invariant and grid induction cover every output. Trace
ownership distinguishes three shared read-only inputs from each thread's output.

`verify-rotary` accepts only this nine-instruction program, matching FP16 rank-two
buffers `[M,D]` and `[M,D/2]`, even positive D, `M*D<2^31`, one thread/block per
output, native warp width and fuel `[8,1,1,1]`. The independent reference uses the
fixed reshape/select/stack expression for interleaved complex multiplication.
Its full operator AST must match at the declared shape before a minimal instance
is used to validate module imports, binding and dtypes. Arbitrary shape-dependent
branches, views, permutations, extra operations and aliases cannot be lifted by
that minimal check. The shape-to-flat-index formalization remains trusted.

All seven libraries are inline in an export. `lark check` regenerates the fixed
source/reference/signature statement and reruns Lean with six final axiom audits.
Only `propext`, `Classical.choice` and `Quot.sound` occur in final proofs. Arithmetic
and half conversions are abstract, with no IEEE or numerical-error theorem.
Source lowering, reference formalization, host contracts and the external
connection between race-free phases and GPU interleavings remain trusted.

## Reproduce

Use Lean **4.19.0** and Python 3.11 or newer, at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-rotary reproduction/rotary/cases/hip/kernel.hip \
  --reference reproduction/rotary/cases/hip/reference.py \
  --task reproduction/rotary/cases/hip/task.json --output /tmp/lark-rotary
python -m lark_kernels check /tmp/lark-rotary
python reproduction/rotary/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-rotary-cpu
python reproduction/rotary/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-rotary-cpu --output /tmp/lark-rotary-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/rotary/run_gpu.py \
  --input /tmp/lark-rotary-input --output /tmp/lark-rotary-device
python reproduction/rotary/summarize.py
```

GPU preparation needs CPU PyTorch and NumPy; the device runner uses standard-library
Python, HIP compiler/headers/runtime, the shared binary FP16 loader and wrapper
validator. SHA-256 binds full probe bytes, every extent, source/reference/task,
wrapper and certificate index. The runner reconstructs the wrapper before compiling.

Six normal-random trials and zero, constant, alternating-sign and uniform probes
check every output against CPU PyTorch with rtol=atol=0.01. All three inputs are
checked byte-for-byte after each launch; all four allocations have 128-byte
guards before/after. Guards check writes; modeled access safety is established
separately in Lean. GPU hosts do not rerun Lean.

The CPU study exports/rechecks both language profiles and four scaling shapes,
then sends arithmetic, parity and pair-index changes directly to Lean after
bypassing the structural profile screen. They fail fixed-program equality. These
are source-binding checks, not the paper's original mutants or semantic diagnoses.

Archives preserve exact executed CPU sources, successful/failed attempts, and
the device runner, validators, binary probes, wrapper and index. The summarizer
checks current statements against archived ones and source/device hash bindings.
Scaling uses one attempt per shape; elapsed verification includes fresh Lean
elaboration and concurrent CPU checks. The largest shapes are proof-only; only
`[256,128]` ran on hardware. No optimized performance or original model-outcome
result is claimed.
