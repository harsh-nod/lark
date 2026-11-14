# Full-size compiled FFN preparation

These are exact inputs from the independently published full-size compiler
study. `input-bindings.json` binds every file to its original archive member.
The first launch computes a 64×256 by 256×1024 matrix product, ReLU and an FP16
store. The second reads that complete 64×1024 FP16 intermediate and multiplies
by a 1024×256 matrix. The supplied reference preserves both FP16 round trips.

The development frontend checks both fixed contracts and losslessly reads all
173 and 171 instructions, including their original loop limits. It keeps grids
65,536 and 16,384, block size 1, warp size 32, and CUDA fuel 1,030 and 4,102.

This is preparation only. Neither compiled-stage execution nor the composed
PTX pipeline has a new correctness proof yet. It adds no accepted certificate,
paper result, original optimized program, IEEE guarantee or NVIDIA execution.
