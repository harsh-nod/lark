# Full-size PTX compilation on CPU

All 25 CUDA source stages across the 17 independent full-size benchmark tasks
compiled to PTX 8.8 and assembled for `sm_80` without a GPU. NVRTC and ptxas
were both NVIDIA 12.9.86. The compiler adds only `#include <cuda_fp16.h>`;
original source/reference/task bytes, shapes, dtypes, geometry and fuels are retained.
Fusion contraction and flush-to-zero were disabled; precise division/square-root
options were enabled. These settings do not establish IEEE equivalence.

The existing LARK PTX reader refused all 25 generated programs: three at its
FP32-only type gate and 22 during tokenization. These are first refusals, not
an exhaustive inventory of unsupported features and not counterexamples.
The reader supports a smaller PTX 8.0 scalar subset; broader FP16, control-flow,
instruction and whole-launch proof support still needs implementation.

There are **zero new PTX proofs, model cohorts, source certificates or GPU
trials**. Assembly does not establish the compiler's semantic refinement,
the generated PTX's correctness, NVIDIA execution or hardware conformance.
The existing four tiny PTX certificates and HIP/CUDA model results remain separate.

`raw.tar.gz` retains the complete 346-file recording, exact compiler input,
PTX, cubins, task/reference sources, logs, toolchain/header hashes and reader
refusals. `first-build.tar.gz` retains the earlier 346-file completed build.
The second build closes the compiler/header inventory; all 25 PTX/cubin pairs
match the first build byte-for-byte. These are repeated builds of the same
25 stages, not 50 independent kernels.

The separate `audit.tar.gz` retains source/task/recording checks, 25 regenerated
reader probes and three compiler-boundary tests. It runs no compiler, model,
Lean or GPU experiment and executes no captured Python. All archive members
and the top-level packet are hash bound. The original paper is not fully reproduced.
