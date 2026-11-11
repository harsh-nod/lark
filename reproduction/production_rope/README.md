# Native in-place vLLM RoPE development study

Both complete HIP adaptations retain vLLM's 512-thread block and strided
query/key loops. Query has 32 heads, key has eight, and each head has 128 FP16
values. Each native thread rotates four query pairs and one key pair in place.
Both interleaved (`IS_NEOX=false`) and split-half (`IS_NEOX=true`) layouts are
covered. The source contract permits 1..65535 contiguous token rows; hardware
measurements use 1, 3, 64 and 256 rows.

The [pinned upstream source](upstream/pos_encoding_kernels.cu) is vLLM commit
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8`, `csrc/pos_encoding_kernels.cu`.
The [provenance](provenance.json) records every fixture hash and the independent
rewrites/departures. As the paper describes, the adaptation receives already
gathered cache rows. This fixed profile selects full128 rotation, inverse=false,
contiguous Q/K and FP16 cache, with no extra rotary offset. It preserves both
mutable buffers, all cache reads, input-before-store order and explicit half
conversions. It runs on HIP wave64. The authors' actual adapted files, shapes,
model dialogues and NVIDIA measurements remain unavailable.

The [program module](../../lean/Lark/NativeRopeProgram.lean) binds both full
50-instruction programs to the pinned scalar machine, seeded Q/K initialization,
read-only cache, geometry and unchanged fuel. The
[address module](../../lean/Lark/NativeRopeAddress.lean) proves both pair
coordinates cover every component exactly, their inverse owner mapping, native
thread ownership and signed-int32 address bounds. The conditional footprint
theorem derives race freedom if every actual access is classified. Its premise
must still be proved from the complete source execution.

The fresh source check builds four local Lean modules, audits 27 library
declarations and nine source results at each of eight layout/row instances
(99 audits total), and rejects nine false Lean claims. Controls change pair
coordinates, loop stride, sine-cache offset, buffer, store, arithmetic, layout
label and mutable-buffer list, or deny a proved inverse. A standalone replay
repeats these checks without Git or any owned compiled cache. Rehashed scope
guards reject invented complete launch/reference proofs or certificates before
source extraction.

The frozen [source packet](results/components-v1/results.json),
[independent replay](results/components-validation-v1/results.json) and
[scope guards](results/component-stage-guards-v1/results.json) retain the checked
statements, source archive, audit logs and refusals. All 57 archived source and
checker files match source revision `84d0ef6ea3e87ac306e21cfbd1f17f164bf804bb`.
The [wheel audit](results/packaging-v1/results.json) matches the reader and all
146 required proof modules for this profile and the earlier softmax results
to that revision, including both new native RoPE modules.

The separate finite interpreter executes each complete source at one and three
rows. It compares all 40,960 symbolic output expressions with an independently
indexed formula, retains all 122,880 access records, checks every thread's halt
at PC49 and the read-only cache, and rejects ten changed source programs. Each
row has 15,360 accesses and 5,120 output values at epoch(grid0,block0,warp0).
The [finite packet](results/symbolic-v1/results.json) preserves all complete
traces and symbolic output lists as compressed, hashed streams.

Both AMD hosts completed 48 paired trials (96 launches per host). The comparison
retains all three upstream device/helper bodies verbatim, substitutes HIP
headers and a plain load for `VLLM_LDG`, and uses identity positions to compare
with the already-gathered input. All allocations have 128-byte guards, and cache
and position buffers are checked unchanged. Every compiler-reported source/header
is captured. Fresh CPU float64 and CPU Torch FP32 audits checked **79,626,240
values**, with zero tolerance failures at `atol=rtol=0.002`, zero Torch FP32 bit
differences and zero adapted/upstream bit differences. These are independent
finite HIP comparisons; the original CUDA binary is not executed. Numerical
controls fully rehash one wrong output, false proof/certificate claims, a missing
trial and a widened tolerance, and reject all five.

The [both-host packet](results/native-v1/results.json) retains runtime reports,
input hashes, compiler inventories and the [fresh CPU audit](results/native-v1/gpu-audit.json).
Full input/output and compiler source captures are available in the
[public release](https://github.com/harsh-nod/lark/releases/tag/native-rope-evidence-20261111).
All four asset bodies were [downloaded anonymously and hashed](results/publication-v1/results.json)
in full, checking 109,450,561 bytes against both the local packets and GitHub's
server digests. The [numerical controls](results/numerical-controls-v1/results.json)
retain all five fully rehashed rejections.

**Complete native launch execution, classification of its universal actual
trace, and source/reference equality are still pending.** This development
issues zero registered source certificates and is outside the immutable v19
paper ledger. It does not add another accepted original production result.
As in the paper, IEEE/rounding/error-bound guarantees are outside formal scope;
floating-point behavior is checked numerically.

```bash
# Python3.11+ and Lean/Lake4.19.0; choose fresh output directories.
python3 -m unittest discover -s tests -p test_native_rope.py -v
python3 reproduction/production_rope/check_program.py --output /tmp/rope-components
python3 reproduction/production_rope/replay_components.py \
  --packet /tmp/rope-components --output /tmp/rope-replayed \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_rope/check_component_stages.py \
  --packet /tmp/rope-components --output /tmp/rope-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_rope/run_symbolic.py --output /tmp/rope-symbolic

# Input preparation and independent CPU audits need NumPy and CPU PyTorch.
python3 reproduction/production_rope/prepare_gpu.py --output /tmp/rope-input
# On each free gfx950/wave64 host, after copying the complete frozen input:
HIP_VISIBLE_DEVICES=0 python3 /tmp/rope-input/run_gpu.py \
  --input /tmp/rope-input --output /tmp/rope-host
python3 reproduction/production_rope/audit_gpu.py --input /tmp/rope-input \
  --host /path/to/mi350 --host /path/to/mi350-2 --output /tmp/rope-audit
python3 reproduction/production_rope/check_gpu_controls.py --input /tmp/rope-input \
  --host /path/to/mi350 --output /tmp/rope-numerical-controls
```
