# Unchanged compiled batched GEMM input

These exact bytes come from the independently published full-size compiler
study: NVRTC 12.9.86, PTX 8.8, sm_80. Every copied member matches raw-files.json.
A [32,64,256] times B [32,256,512] produces [32,64,512], all FP16, with
grid 1048576/block one/warp 32 and unchanged CUDA fuel [1030,1,1,1].

The development reader preserves all 138 instructions and the real backward
branch to instruction 29. The separate [BMM development profile](../../BATCHED.md)
now has checked Lean proofs for complete actual-source execution of every lane,
all sixteen iterations, the closed ordered reference, actual-trace race freedom
and preservation outside the output. Source-only export/replay and publication
validation are tracked separately there. These independent results add no
original model outcome, legacy registered profile or NVIDIA execution claim.
