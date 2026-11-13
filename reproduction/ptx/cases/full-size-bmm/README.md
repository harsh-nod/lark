# Unchanged compiled batched GEMM input

These exact bytes come from the independently published full-size compiler
study: NVRTC 12.9.86, PTX 8.8, sm_80. Every copied member matches raw-files.json.
A [32,64,256] times B [32,256,512] produces [32,64,512], all FP16, with
grid 1048576/block one/warp 32 and unchanged CUDA fuel [1030,1,1,1].

The development reader preserves all 138 instructions and the real backward
branch to instruction 29. Grammar acceptance is not a kernel proof, registered
certificate, model outcome or NVIDIA execution. Complete actual-source launch,
reference and race proofs remain required.

Initial Lean lemmas check the program length, backward branch and final ret,
and derive batch/row/column addressing and valid input indices for every output
lane and all 256 reduction indices. They do not establish complete execution.
