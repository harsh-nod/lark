# Native in-place fused add RMSNorm

This is an independent development study of the paper's
`sglang_fused_add_rmsnorm` family. **No complete source certificate is claimed.**
It adds initialized mutable-buffer interfaces, fixed-source identity and address
proofs, a conditional footprint theorem, and numerical validation on both AMD
hosts. Whole-launch execution, actual-trace classification and reference
equivalence remain proof obligations.

The [provenance record](provenance.json) pins SGLang commit
`fc32cbff6983c7573f4b60eab8b44815668130a0`, independently selected before the
preprint date. Its
[wrapper](https://github.com/sgl-project/sglang/blob/fc32cbff6983c7573f4b60eab8b44815668130a0/python/sglang/kernels/aot/csrc/elementwise/fused_add_rms_norm_kernel.cu)
calls FlashInfer. The pinned
[build file](https://github.com/sgl-project/sglang/blob/fc32cbff6983c7573f4b60eab8b44815668130a0/python/sglang/kernels/aot/CMakeLists.txt)
selects FlashInfer commit `bc29697ba20b7e6bdb728ded98f04788e16ee021`; its
[actual kernel and host launch](https://github.com/flashinfer-ai/flashinfer/blob/bc29697ba20b7e6bdb728ded98f04788e16ee021/include/flashinfer/norm.cuh)
are retained locally with their licenses. This does not identify the authors'
original adapted source or experiment revision.

The fixed profile uses FP16 `[rows,16384]` input/residual buffers, FP16 weights,
`1 <= rows <= 255`, 1,024 threads and physical wave64. Each physical wave contains
two complete logical32 XOR-reduction groups. The source retains two block
barriers, eight-element ownership and both vector rounds. Identical shared
stores are guarded by their unique writer; vector accesses are scalarized.
The host supplies three mutually disjoint, contiguous, aligned buffers.

Both `input` and `residual` start initialized and are updated in place. The
kernel computes their sum in FP32, stores its FP16-rounded form in `residual`,
and retains the **unrounded FP32 sum** in shared memory for normalization into
`input`. Reading back the rounded residual for that last step changes the
floating-point algorithm. Weight remains read-only.

## Proof components and limits

The scoped development reader maps the two in-out buffers to writable cells of
the existing machine and initializes them using `LarkInOut.initial`. The pinned
scalar/collective machine definitions and ordinary reader acceptance rules are
unchanged. The ordinary task parser still refuses this in-out task; there is no
new registered verification profile.

The [frozen component packet](results/components-v1/results.json) freshly builds
11 local Lean modules, replays the frozen Python reader, checks exact IR/layout/
geometry/fuel/interface binding and audits 40 results. Nine false claims are
rejected, including omitted mutable initialization, read-only weight writes,
foreign-owner initialization, missing barriers and changed source operations.
An [independent archive replay](results/components-validation-v1/results.json)
rebuilds from an empty directory with Git unavailable and no seeded own Lean
objects, repeating the reader check and all nine refusals.

The sufficient footprint theorem proves race freedom **if** every actual access
satisfies its classification. Deriving that classification and successful
execution from the full source remains open. A separate finite value-erased run
for one row halts at PC71/epoch2 and checks 115,777 accesses; it is not a universal
trace theorem, numerical evaluation or source certificate.

```bash
# Lean 4.19.0, standard library only; fresh output outside the checkout:
python3 reproduction/production_fused_rmsnorm/check_program.py --output /tmp/fused-components
python3 -m unittest discover -s tests -p test_native_fused_rmsnorm.py -v
```

## Finite AMD results

Each host ran 24 paired trials: rows 1, 3, 64 and 255, with six finite input
families including signed zeros, halfway rounding, cancellation and mixed
magnitudes. One method is the scalarized HIP adaptation. The comparison retains
the selected upstream template body verbatim while explicitly replacing CUDA
shuffle/rsqrt and vector helpers with HIP helpers. It is not unchanged NVIDIA
kernel execution or a proof of helper/compiler equivalence.

| Host | Normalized CPU-double comparisons | Exact residual-bit comparisons | Failures |
| --- | ---: | ---: | ---: |
| mi350 | 63,504,384 | 63,504,384 | 0 |
| mi350-2 | 63,504,384 | 63,504,384 | 0 |

The independent audit recomputes every reference from the original FP16 input,
residual and weight bytes. Normalized values use `0.002 + 0.002 * abs(reference)`;
maximum absolute error is `0.0037352077129462202`. Residual storage matches the
FP32-add/FP16-store oracle exactly for both methods. All allocation guards and
read-only weights pass. Compiler-reported inputs are captured: 318 files on
`mi350`, 313 on `mi350-2`.

Per host, normalized method streams differ at 3,084,098 signed-zero values and
475 other values, each of the latter by one FP16 ULP. The residual streams are
bit-identical. All four streams match between hosts. These finite observations
are not an IEEE equivalence or numerical-error theorem.

Three fully rehashed audit controls reject an invented source certificate,
original-paper completion and a nonfinite output. No paid endpoints or model
calls are used. The original production adaptation, historical agent results,
NVIDIA measurements and full upstream API remain unreproduced.

The [numerical/source packet](results/native-v1/report.json) binds experiment-code
commit `d35cd2042d839fa07d29ee1f76bfa75f26c4893d`. Individual compressed streams
preserve the prepared operands, references and all four outputs on each host;
compiler-reported dependencies and the exact comparison driver are included.
The [numerical replay validation](results/numerical-validation-v1/results.json)
restores the packet outside the checkout and regenerates its audit report byte
for byte. A fully rehashed archive-traversal control is rejected before writing
the parent-directory target. The replay uses Python and NumPy, with no GPU,
Lean, Git or model calls:

```bash
python3 reproduction/production_fused_rmsnorm/replay_packet.py \
  --packet reproduction/production_fused_rmsnorm/results/native-v1 --output /tmp/fused-replay
```

```bash
python3 reproduction/production_fused_rmsnorm/prepare_gpu.py --output /tmp/fused-input
# On each available AMD host after copying that frozen directory:
HIP_VISIBLE_DEVICES=0 python3 /tmp/fused-input/run_gpu.py --input /tmp/fused-input --output /tmp/fused-device
# Retrieve both host directories, then recompute all references on a CPU:
python3 reproduction/production_fused_rmsnorm/audit_gpu.py --input /tmp/fused-input \
  --host /tmp/fused-mi350 --host /tmp/fused-mi350-2 --output /tmp/fused-audit.json
python3 reproduction/production_fused_rmsnorm/check_audit_controls.py --input /tmp/fused-input \
  --host /tmp/fused-mi350 --output /tmp/fused-controls
```
