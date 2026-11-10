# AMD shuffle and matrix-core conformance

This independently extends the paper's per-operation hardware-testing category.
It records concrete wave64 shuffle and one MFMA fragment layout on two MI350X
hosts. It does not extend the Lean instruction set. [Results](RESULTS.md).

The shuffle contract follows AMD's [HIP language reference](https://rocm.docs.amd.com/projects/HIP/en/latest/how-to/hip_cpp_language_extensions.html)
and [shuffle builtin reference](https://rocm-handbook.amd.com/projects/amd-rocm-optimization-guide/en/develop/compiler-builtins/cross-arch/wavefront-ref/shuffle-builtins.html).
MFMA uses the native `__builtin_amdgcn_mfma_f32_16x16x16f16` builtin, default
modifiers and a full 64-lane wave. AMD documents the general instruction family
and output layouts in its [CDNA4 reference](https://rocm-handbook.amd.com/projects/amd-rocm-optimization-guide/en/develop/compiler-builtins/cdna/cdna4-dense-mfma-builtins.html).
The [AMD matrix instruction calculator](https://github.com/ROCm/amd_matrix_instruction_calculator)
is another primary reference for fragment layouts. The archived compiler assembly
confirms the native MFMA instruction was actually emitted.

For physical lane `l` and item `u` (0..3), the tested FP16 A fragment holds
`A[l % 16, 4*(l/16)+u]`, and B holds `B[4*(l/16)+u, l%16]`. The FP32 C/D
fragment holds output coordinate `[4*(l/16)+u, l%16]`. Independent CPU products
are packed into these slots; the GPU kernel directly loads vectors and issues
the builtin, without reproducing the CPU's coordinate formulas.

```bash
python3 reproduction/collective_conformance/prepare.py --output /tmp/collective-input
cp reproduction/collective_conformance/{probes.hip,run_gpu.py} /tmp/collective-input/
# Copy the prepared directory to an idle ROCm/gfx950 host, then:
HIP_VISIBLE_DEVICES=0 python3 /tmp/collective-input/run_gpu.py \
  --input /tmp/collective-input --output /tmp/collective-device
```

Only standard-library Python and `hipcc` are required. The uncompressed dataset
uses about 194 MiB and the result about 65 MiB; archives compress the basis
probes well. Inputs/configurations and all outputs have 128-byte prefix/suffix
guards. MFMA operands are finite, exactly representable basis or small random
values; this deliberately tests layout without claiming general rounding behavior.

This is finite hardware evidence for one architecture/form, rather than a Lean
proof, general instruction semantics, formal collective integration, or a
reproduction of the authors' unavailable table and probes. The main verifier
continues to refuse unsupported shuffles and tensor-core operations.
