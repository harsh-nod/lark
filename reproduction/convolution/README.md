# Full-size valid Conv2D and depthwise induction

This independent extension certifies FP16 Conv2D
`[1,32,8,8] * [8,32,3,3] -> [1,8,6,6]` and depthwise convolution
`[1,32,16,16] * [32,1,5,5] -> [1,32,12,12]`, groups=32. These match the
independent contracts at the paper's largest workload dimensions. Separate
HIP/CUDA exports are checked by Lean. [Results](RESULTS.md), [evidence](results/),
[paper coverage](../COVERAGE.md).

Programs use one scalar thread/block per output and a serial FP32 reduction,
with FP16 inputs/output. They differ from the authors' optimized kernels/launches.
Only HIP is executed on hardware; CUDA is checked by CPU Lean.

## Proof boundary

The [Convolution library](../../lean/Lark/Convolution.lean) supplies address
functions, bounds and primitive index-evaluation proofs to the existing
`LarkDot.Profile`. The dot-loop/grid theorem concludes the actual unchanged
`LarkNonlinear.Correct`: completion, race freedom and every output, for every
input and arbitrary outside memory, under any scalar-operation interpretation.

The input proof decodes channel and spatial/kernel rows/columns using division
and remainder. Valid-window bounds establish that each row/column stays inside
the input. Every signed 32-bit multiplication/addition and declared buffer bound
is checked. Dense reduction channels come from the reduction index; depthwise
channels come from the output index. Weights use output-channel-major flat rows.
Profiles assume no loop summary, launch equality or correctness.

`verify-convolution` accepts only matching positive rank-four FP16 shapes,
square NCHW input/kernel, batch=1, stride=1, no padding/bias, groups=1 or depthwise,
one thread/block per output, native warp width, complete counted-loop fuel and
all allocation sizes below 2^31. The one-channel/one-output-channel case uses
the depthwise indexing profile; both operators have group count 1 there.

The closed reference AST is exactly
`torch.conv2d(x.float(),w.float(),groups=G).half()` with the matching G.
The full operator/group choice must match before a minimal instance is used to
validate imports, binding and dtypes. Added padding, views, changed grouping or
arbitrary shape-dependent code cannot pass that minimal check. The NCHW tensor
operation's flat-index formalization remains trusted.

Exports include all six required libraries inline. `lark check` regenerates the
fixed source/reference/signature statement and reruns Lean with six final axiom
audits. Only `propext`, `Classical.choice` and `Quot.sound` occur in final proofs.
Arithmetic/half conversions are abstract, with no IEEE or numerical-error theorem.
Source lowering, reference formalization, host contracts and the external link
between race-free phases and GPU interleavings remain trusted.

## Reproduce

Use Lean **4.19.0** and Python 3.11 or newer, at the repository root:

```bash
export LARK_LEAN=/path/to/lean-4.19.0/bin/lean
python -m lark_kernels verify-convolution \
  reproduction/convolution/cases/hip/depthwise_conv/kernel.hip \
  --reference reproduction/convolution/cases/hip/depthwise_conv/reference.py \
  --task reproduction/convolution/cases/hip/depthwise_conv/task.json \
  --output /tmp/lark-depthwise
python -m lark_kernels check /tmp/lark-depthwise
python reproduction/convolution/run_cpu.py --lean "$LARK_LEAN" --output /tmp/lark-conv-cpu
python reproduction/convolution/prepare_gpu.py --lean "$LARK_LEAN" \
  --cpu /tmp/lark-conv-cpu --output /tmp/lark-conv-input
HIP_VISIBLE_DEVICES=0 python3 reproduction/convolution/run_gpu.py \
  --input /tmp/lark-conv-input --output /tmp/lark-conv-device
python reproduction/convolution/summarize.py
```

Preparation needs CPU PyTorch/NumPy; the GPU runner needs standard-library
Python and HIP compiler/headers/runtime. The shared binary FP16 loader binds
full probe bytes and every extent with SHA-256. The wrapper validator checks
finite values, allocation shapes, tolerances, all ten trials/family and
source/reference/task hashes against the CPU certificate index. The wrapper is
reconstructed before compiling the exact certified source.

Six normal-random trials and zero, constant, alternating-sign and uniform probes
check all outputs against CPU PyTorch with rtol=atol=0.01. Inputs are checked
byte-for-byte after each launch; all three allocations have 128-byte guards
before/after. Guards check writes; modeled access safety is established separately
in Lean. GPU hosts do not rerun Lean.

The CPU study records four baseline proofs/rechecks, five scaling shapes and
three changed programs sent directly to Lean after bypassing the structural
profile screen. Arithmetic, kernel-row and output-channel changes fail fixed-
program equality. These are source-binding checks, not the original mutants or
semantic diagnosis/channel counts. Archives preserve exact executed CPU sources,
all attempts and diagnostics, and the device runner, validators, binary probes,
wrapper and index. The summarizer checks archived statements and source bindings.

Scaling uses one attempt per shape with concurrent CPU checks included in elapsed
verification time. The largest shapes are symbolic only; they allocate no arrays
and execute no device work. Only the two stated paper-size contracts ran on GPUs.
No optimized performance or original model-outcome result is claimed.
