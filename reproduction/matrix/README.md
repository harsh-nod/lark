# Full-size GEMM and batched GEMM induction

This independent extension certifies FP16 GEMM `[64,256] @ [256,512]` and
batched GEMM `[32,64,256] @ [32,256,512]`, matching the paper's largest workload
dimensions. HIP and CUDA have separate source-bound certificates.
[Results](RESULTS.md), [evidence](results/), [paper coverage](../COVERAGE.md).

The launch uses one scalar thread/block per output and serial FP32 accumulation.
These programs differ from the paper's optimized kernels, launches and harness.
HIP is executed on both MI350X hosts; CUDA is checked by Lean on the CPU.

## What Lean checks

The [generic dot-loop library](../../lean/Lark/DotLoop.lean) proves the actual
`LarkNonlinear.runLaunch` and `Correct`. Profiles supply input sizes, address
functions, their bounds, and primitive index-evaluation proofs. A profile cannot
assume a loop summary, launch equality, or correctness. The loop/grid induction
establishes completion, race freedom and every output for all inputs and arbitrary
outside memory, under any scalar-operation interpretation.

The [matrix library](../../lean/Lark/Matrix.lean) instantiates those requirements
for row-major GEMM and equal-batch BMM, including every signed 32-bit intermediate
in division, remainder, multiplication and address addition. The tensor reference
is a separate left-fold dot product mapped over the full output footprint. Source
and reference indexing are linked through primitive evaluation theorems checked
by Lean. The existing machine and earlier proof libraries are unchanged.

`verify-matrix` restricts source to the canonical nine-instruction program, FP16
rank-two or rank-three matching matmul shapes, one thread per output, native
warp width, exact counted-loop fuel and all allocation sizes below 2^31. BMM
requires equal batch dimensions; broadcast, aliases, shape-dependent branches
and extra operations are refused. The closed reference AST is exactly
`(a.float() @ b.float()).half()` with validated imports and binding.

Standalone exports contain all five libraries inline. `lark check` regenerates
the statement from the fixed source/reference/signature and reruns Lean with six
final axiom audits. Only `propext`, `Classical.choice` and `Quot.sound` occur in the
final proofs. Arithmetic/half operations remain abstract, with no IEEE rounding or
numerical-error theorem. Source lowering, the closed Torch formalizer, host
contracts and race-free-phase correspondence with hardware remain trusted.

## Reproduce

Use Lean **4.19.0** and Python 3.11 or newer, at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-matrix reproduction/matrix/cases/hip/bmm/kernel.hip \
  --reference reproduction/matrix/cases/hip/bmm/reference.py \
  --task reproduction/matrix/cases/hip/bmm/task.json --output /tmp/lark-bmm
python -m lark_kernels check /tmp/lark-bmm
```

The CPU study exports four baseline certificates, independently rechecks them,
checks five scaling shapes and sends three changed actual IR programs to Lean
after bypassing the structural profile screen. Those changed programs fail the
fixed-program equality obligation. This is source binding, not the paper's
original mutation set or semantic diagnosis/rejection-channel counts.

```bash
python reproduction/matrix/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-matrix-cpu
python reproduction/matrix/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-matrix-cpu --output /tmp/lark-matrix-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/matrix/run_gpu.py \
  --input /tmp/lark-matrix-input --output /tmp/lark-matrix-device
python reproduction/matrix/summarize.py
```

Input preparation needs CPU PyTorch and NumPy; the device runner uses
standard-library Python and HIP compiler/headers/runtime. Probe inputs and CPU
expected outputs are little-endian FP16 in `tensors.f16`; JSON binds the full file
and every extent with SHA-256. The loader rejects altered bytes or invalid extents,
and the shared wrapper validator checks finite values, declared shapes, tolerances,
all ten trials/family, and source/reference/task hashes against the CPU certificate
index. The wrapper is reconstructed before compiling the certified source bytes.

Six normal-random trials and zero, constant, alternating-sign and uniform probes
check every output with rtol=atol=0.01. Every allocation has 128-byte guards and
all input bytes are checked after each launch. Guards detect writes; the modeled
Lean proof separately establishes access safety. GPU hosts do not rerun Lean.

The CPU archive preserves all proof attempts/recheck logs and failed changed
programs; a separate snapshot preserves the exact executed CPU source. The device
bundle includes its binary probes, source/reference/task, wrapper, validator and
runner. Receipts hash those inputs and the compiled library. The largest scaling
cases are symbolic proofs only: they allocate no matrices and execute no GPU work.
Timings include Python/fresh Lean elaboration with other CPU checks running;
one attempt per shape is recorded. No optimized performance result is claimed.
