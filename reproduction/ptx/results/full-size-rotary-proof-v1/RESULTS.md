# Full-size compiled interleaved RoPE development proof

One independent source-bound abstract PTX proof, four retained fresh checks,
32 fresh owned module builds, three rechecks, four direct Lean refusals and
17 coherently rehashed SDK recording refusals. All 17 earlier development
attempts (six passing partial checks, eleven failures), preparation and the
failed wheel preflight are retained in full with their original manifests.
No failed or partial check is counted as an official positive proof.

The unchanged FP16 shapes are x/out[256,128] and cosine/sine[256,64], with
grid 32768, block 1, warp 32 and original CUDA fuel [8,1,1,1]. All 51 source
instructions and 52 physical registers are retained. Each lane executes its
actual 41-instruction path, with five memory accesses. The full launch has
race-free access traces, preserves memory outside the output and matches an
independent shape-checked reshape/select/stack/arithmetic/half tensor denotation.

These are recorded checks; archive validation runs no Lean, model or GPU.
The installed environment is retained completely. Its file symlinks are
archived as ordinary byte data, and all original link targets, including the
directory link, are recorded in runtime-links.json. Captured code is data.
No proof limit, original shape, geometry or fuel was increased or reduced.

The proof uses abstract scalar operations and trusted parsing, ABI/pointer
correspondence and aligned disjoint non-wrapping allocations. It establishes
no IEEE/error bound, NVIDIA execution/conformance, original optimized-kernel
result, model success, legacy profile registration or full-paper reproduction.
Anonymous public verification and source CI remain separate publication gates.
