# Full-size Linear induction

This independent extension certifies FP16 Linear
`[64,256] @ [256,512] + [512] -> [64,512]`, matching the paper's largest
dimensions, with separate HIP and CUDA source-bound certificates.
[Results](RESULTS.md), [evidence](results/), [paper coverage](../COVERAGE.md).

The launch uses one scalar thread/block per output and serial FP32 accumulation.
Its biased store reads the third input at the output column before converting
the sum to FP16. These programs differ from the authors' optimized kernel and
launch. Only HIP is executed on hardware; CUDA is checked by Lean on the CPU.

## Proof boundary

The [Bias library](../../lean/Lark/Bias.lean) extends the checked address profile
with bias size/index/bounds and a primitive bias-index evaluation proof. Its
counted-loop, store and grid induction conclude the actual existing
`LarkNonlinear.Correct`: completion, race freedom and every output, for every
input and arbitrary outside memory. Trace ownership covers all three read-only
inputs and each thread's unique output. The standalone tensor reference is a
left-fold dot product plus promoted broadcast bias, converted to half.

The existing machine and earlier proof libraries are unchanged. Bias profiles
cannot assume an execution summary or correctness. `verify-linear` accepts only
the nine-instruction profile, matching positive FP16 matrix/vector shapes,
allocation sizes below 2^31, native warp width, one thread/block per output and
fuel `[4*K+6,1,1,1]`. The reference AST is exactly
`(a.float() @ b.float() + bias.float()).half()` with validated imports/binding.
Views, indexing, shape-dependent branches, aliases and extra operations are refused.

All six libraries are inline in an export. `lark check` regenerates the statement
from fixed source/reference/signature bytes and reruns Lean with six final axiom
audits. Only `propext`, `Classical.choice` and `Quot.sound` occur in final proofs.
Arithmetic and conversions remain abstract; IEEE rounding/error bounds are
outside the theorem. Source lowering, the closed reference formalizer, host
contracts and hardware correspondence for race-free phases remain trusted.

## Reproduce

Use Lean **4.19.0** and Python 3.11 or newer, at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-linear reproduction/linear/cases/hip/kernel.hip \
  --reference reproduction/linear/cases/hip/reference.py \
  --task reproduction/linear/cases/hip/task.json --output /tmp/lark-linear
python -m lark_kernels check /tmp/lark-linear
python reproduction/linear/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-linear-cpu
python reproduction/linear/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-linear-cpu --output /tmp/lark-linear-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/linear/run_gpu.py \
  --input /tmp/lark-linear-input --output /tmp/lark-linear-device
python reproduction/linear/summarize.py
```

GPU input preparation needs CPU PyTorch and NumPy; the device runner needs
standard-library Python and HIP compiler/headers/runtime. It reuses the
[binary FP16 loader](../matrix/bundle.py) and shared wrapper validator. SHA-256
binds the binary file and each extent, source/reference/task bytes and the CPU
certificate index. The wrapper is reconstructed before compiling.

Six normal-random trials and zero, constant, alternating-sign and uniform probes
check every output against CPU PyTorch with rtol=atol=0.01. All three inputs are
checked byte-for-byte after each launch, with 128-byte guards before/after all
four allocations. Guards detect writes; modeled access safety is established
separately in Lean. GPU hosts do not rerun Lean.

The CPU study records both baseline proofs/rechecks, three scaling shapes and
three changed programs sent directly to Lean after bypassing the structural
profile screen. Arithmetic, wrong bias-column and omitted-bias variants fail
fixed-program equality. These are source-binding checks, not the paper's original
mutants, semantic diagnoses or rejection-channel counts.

Archives preserve exact executed CPU sources, proof attempts and diagnostics,
and the device runner/validator, probes, wrapper and certificate index. The
summarizer checks current statements against archived ones and device bindings
against the source bundle. Scaling uses one attempt per shape, with concurrent
CPU validation included in elapsed verification times. The million-term case is
proof-only; only the stated 64×256×512 shape ran on hardware. No optimized
performance or original model-outcome result is claimed.
