# Unchanged compiled Linear input

These exact source, reference and task bytes come from the independently
published full-size compiler study: NVRTC 12.9.86, PTX 8.8, sm_80. Every copied
member is checked against its original `raw-files.json` entry.

The task is `(a.float() @ b.float() + bias.float()).half()` with FP16
`a[64,256]`, `b[256,512]`, `bias[512]` and `out[64,512]`. Grid 32768, block one,
warp 32 and CUDA fuel `[1030,1,1,1]` remain unchanged.

The development reader preserves all 179 instructions, 189 register declarations,
the actual branch from PC 167 to PC 50, and the bias-reading epilogue. It adds
data constructors for `cvt.s64.s32` and `shl.b64`. This is grammar preparation,
not a kernel certificate, registered profile, model outcome or NVIDIA execution.
Formal execution, complete-launch, reference and actual-trace race proofs remain.
