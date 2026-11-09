# Input format

A task is independent of the kernel. `buffers` gives kernel argument order;
the reference function takes only input buffers, in that order, and returns
one tensor per output buffer. Multiple outputs use a Python tuple.

```json
{
  "name": "vector_add",
  "entry": "vector_add",
  "language": "cuda",
  "buffers": [
    {"name": "x", "role": "input", "shape": [4], "dtype": "float32"},
    {"name": "y", "role": "input", "shape": [4], "dtype": "float32"},
    {"name": "out", "role": "output", "shape": [4], "dtype": "float32"}
  ],
  "launch": {"grid": 2, "block": 2, "warp": 32},
  "fuel": [128, 16, 16, 16]
}
```

Shapes are positive literal dimensions, stored contiguously in row-major order.
Source buffers are flat `float*` parameters, even for multidimensional tensors.
Scalar tensor results may occupy an output buffer of shape `[1]`.

Roles are `input`, `output`, or `scratch`. Input writes are refused. Output and
scratch cells begin with arbitrary contents; scratch is not extracted and the
reference cannot read it. In-place and aliased buffers are not supported.

Languages are `cuda` and `hip`. The default warp width is 32 for CUDA and 64
for HIP; HIP can select 32 explicitly. The host must select the same width.
The concrete launch is one-dimensional and must have at most 256 threads.
Each global or shared buffer has at most 4096 cells. These are admission
limits, not a promise that every admitted size proves quickly.

Fuel is ordered `[lane, warp, block, grid]`. Each bound is a positive integer.
The semantics faults at zero fuel; increasing fuel does not become an
assumption about termination. Completion within that supplied fuel is part of
the checked theorem.

The source grammar permits one non-template kernel, optionally `extern "C"`,
with `__global__ void` and float pointer arguments. Declarations are `int`,
`float`, optional `const`, or `__shared__ float name[literal]`. There are no
shadowed variables, macros, includes, helper functions, casts, or arbitrary
pointer expressions. Statements include assignment, `+=`, `-=`, `*=`, index
increment/decrement, braced `if`/`else`, braced `while`, barriers, and `return;`.
The smaller grammar is intentional: unknown syntax never falls through to
guessed semantics.

The reference grammar permits `import torch` and one undecorated function,
ordinary tensor assignments, and a return. Supported operators are `+`, `-`,
`*`, and rank-2 or rank-3 `@`. Calls are `torch.relu`, `torch.maximum`, `torch.sum`,
`torch.flip(..., [0])`, `torch.matmul`, `torch.bmm`, and corresponding tensor methods
where appropriate, plus `.reshape(...)` and `.view(...)`. Rank-3 products require
matching batch sizes. Fixed-shape broadcasting follows trailing dimensions of
size one; dynamic Python control is unsupported. `torch.conv2d(x, weight,
groups=literal)` supports NCHW inputs and OIHW weights with stride one, valid
padding, dilation one, and no bias. Other convolution options are refused.

Run `lark inspect` with the same input arguments as `verify` to translate and
perform symbolic preflight without Lean. Its output explicitly says
`preflight-only`; it is never a proof result.

Exit codes: `0` for success, `1` for a failed Lean proof attempt, `2` for
unsupported input, failed preflight, configuration, or integrity failures.
Only a report with `status: verified` issued after Lean's axiom audit is an
accepted certificate. A rejection can mean an unsupported but correct kernel.
