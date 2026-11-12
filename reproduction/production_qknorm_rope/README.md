# Native fused Q/K normalization and RoPE development study

This independent adaptation follows the paper's stated out-of-place departure
for `vllm_fused_qknorm_rope`. It reads FP16 QKV `[tokens,48,128]` with Q32/K8/V8
heads, FP16 Q/K weight vectors and already-gathered FP16 cosine/sine rows. It
writes one new `[tokens,40,128]` Q/K buffer. The input, including all V heads,
stays unchanged. Both interleaved and split-half layouts are implemented.

The source is pinned to vLLM
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8`,
[`csrc/fused_qknorm_rope_kernel.cu`](upstream/csrc/fused_qknorm_rope_kernel.cu).
The [provenance](provenance.json) records the independent rewrites, departures
and file hashes. The authors' actual adapted source, parameters, proof project,
model conversations and NVIDIA measurements remain unavailable.

The adaptation retains the native 256-thread block and five blocks per token.
Each logical 32-lane group handles one head, and each lane holds four contiguous
values. Four native wave64s cover eight heads per block. Every input element is
converted to FP32, accumulated in the original per-lane order, reduced by the
five XOR stages at masks16/8/4/2/1 with width32, and multiplied by the RMS scale
and the appropriate weight before rotation. No intermediate half rounding is
inserted between normalization and RoPE. Split-half rotation retains four
cross-lane exchanges, unary negation, and both synchronization points. All
physical waves contain complete adjacent logical groups; no padding is needed.

The [program module](../../lean/Lark/NativeQKNormRopeProgram.lean) declares both
complete source programs: 88 instructions with five shuffles for interleaved,
107 instructions with nine shuffles and two warp barriers for split-half. The
[address module](../../lean/Lark/NativeQKNormRopeAddress.lean) proves native
head/lane mapping, complete output coverage, unique thread ownership, input
bounds, exclusion of V-head reads and signed-int32 bounds for every supported
token count `1..65535`. A footprint theorem derives race freedom under an
explicit actual-access classification premise. It does not discharge that
premise or prove complete execution.

The execution development now checks the actual first 24 scalar instructions,
the sequential 64-lane preparation fold, and all five logical-width-32 XOR
snapshots. Both layouts have a checked scalar continuation from the last
snapshot through the final add, RMS scale, four weight indices, Q/K weight
selection, four weight reads, and eight source-order normalization products.
For split-half, the actual wave scheduler is connected through normalization
to the first warp barrier at PC59. Its four normalized values match the
source-order five-stage reduction expression; its prefix records 512 reads,
preserves memory and epochs, and is race-free from an initial state. This is
a prefix proof: rotary exchanges, cache loads, stores, complete block/grid
execution, dense reference equality and registered certificates remain open.

`check_execution_prefix.py` rebuilds the dependency closure from fresh copied
sources, audits the printed theorem axioms, and binds these partial execution
theorems to both complete translated HIP sources at 1, 3, 256 and 65,535 rows.
The normalization-prefix check builds 30 Std-only modules and checks 245 library
axiom audits plus 104 source-bound audits across those eight instances.
The historical component packets below retain their original, narrower scope.

The component study builds six Std-only modules, checks 31 library declarations
and nine source declarations at each of eight layout/row instances (103 axiom
audits), and rejects nine false Lean claims. Its standalone replay rebuilds
without Git or a seeded owned proof cache. Ten fully rehashed scope controls
reject invented complete-launch/reference proofs or certificates before source
extraction. Five unit tests check the closed host/reference boundary, including
preservation of the ordinary HIP reader's synchronization restrictions.

The complete finite interpreter checks 40,960 output expressions and all
184,320 accesses at one and three rows in both layouts. Each result is compared
with an independently indexed source-order reduction tree and rotation. The
packet retains complete access traces and lossless expression DAGs, and rejects
15 source changes. This checks finite source execution; it is not a universal
launch theorem or a dense-reference algebra proof.

Both AMD hosts completed 48 paired trials, or 96 launches each, at rows1/3/64/256
with six input patterns and both layouts. The comparison retains the selected
upstream kernel body, common helpers and conversion header; packed conversions
remain in that comparison. Frozen official Torch headers provide its FP16
carrier. Every allocation has 128-byte guards, all adapted inputs and position
IDs are checked unchanged, and upstream V heads are checked unchanged. The
complete compiler-reported include/source closure is captured.

Fresh CPU float64 and Torch FP32 references check **79,626,240 output values**
with zero failures at `atol=rtol=0.002` and zero adapted/upstream bit differences.
The FP16 bits of 3,948 audited output values differ from rounded Torch FP32
results; these comparisons pass tolerance.
Six fully rehashed numerical controls reject a wrong output, invented proofs or
certificate, a missing trial and a widened tolerance without new GPU launches.

**Complete native execution, classification of its universal actual trace and
dense-reference equality remain pending.** This development issues zero source
certificates and is outside the immutable v19 paper ledger. As in the paper,
IEEE/rounding/error guarantees are outside formal scope. This independent
adaptation does not reproduce an original production acceptance or model result.

The frozen [component packet](results/components-v1/results.json),
[independent replay](results/components-validation-v1/results.json),
[scope guards](results/component-stage-guards-v1/results.json) and
[finite values/traces](results/symbolic-v1/results.json) retain the checked
statements and complete finite expression DAGs. The
[both-host packet](results/native-v1/results.json) and
[six numerical controls](results/numerical-controls-v1/results.json) retain the
runtime and CPU audit results. Full raw inputs, output streams, compiler captures
and binaries are in the
[public release](https://github.com/harsh-nod/lark/releases/tag/native-qknorm-rope-evidence-20261111).
All ten [CI jobs](https://github.com/harsh-nod/lark/actions/runs/43112261267) passed
at source revision `c9a7a242de6696e4c9c1aa402d7046b3db2518d9`.
The [publication receipt](results/publication-v1/results.json) binds all 70
archived source files to that revision and records full anonymous downloads of
all four release assets: 111,245,855 bytes matched the local hashes and GitHub's
server digests. It also binds all six evidence manifests and the passing CI
responses.

```bash
# Python3.11+ and Lean/Lake4.19.0; use fresh output directories.
python3 -m unittest discover -s tests -p test_native_qknorm_rope.py -v
python3 reproduction/production_qknorm_rope/check_program.py --output /tmp/fused-qk-components
python3 reproduction/production_qknorm_rope/check_execution_prefix.py \
  --output /tmp/fused-qk-execution-prefix --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/replay_components.py \
  --packet /tmp/fused-qk-components --output /tmp/fused-qk-replayed \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/check_component_stages.py \
  --packet /tmp/fused-qk-components --output /tmp/fused-qk-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_qknorm_rope/run_symbolic.py --output /tmp/fused-qk-symbolic

# Input preparation and independent CPU audits need NumPy and CPU PyTorch.
python3 reproduction/production_qknorm_rope/prepare_gpu.py --output /tmp/fused-qk-input
# Copy the whole frozen input to each free gfx950/wave64 host first.
HIP_VISIBLE_DEVICES=0 python3 /tmp/fused-qk-input/run_gpu.py \
  --input /tmp/fused-qk-input --output /tmp/fused-qk-host
python3 reproduction/production_qknorm_rope/audit_gpu.py --input /tmp/fused-qk-input \
  --host /path/to/mi350 --host /path/to/mi350-2 --output /tmp/fused-qk-audit
python3 reproduction/production_qknorm_rope/check_gpu_controls.py --input /tmp/fused-qk-input \
  --host /path/to/mi350 --output /tmp/fused-qk-numerical-controls
```
