# Full-size GEMM input bytes

These are the unchanged GEMM PTX, reference and contract from the published
[CPU compilation study](../../results/full-size-compilation-v1/RESULTS.md).
The original archive paths are `cases/gemm/kernel/kernel.ptx`,
`cases/gemm/original/reference.py` and `cases/gemm/original/task.json` in its
`raw.tar.gz`. The source bindings preserve each file's exact bytes.

The shapes are FP16 `[64,256] @ [256,512] -> [64,512]`; the launch is
grid32768/block1/warp32 and the separate CUDA fuel is `[1030,1,1,1]`.
The actual PTX has 171 instructions and a backward branch at instruction164
to instruction47. A lossless reader and additional integer-operation lemmas
are development steps. They do not establish whole-kernel correctness or
reproduce an original paper result.
