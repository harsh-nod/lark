# Native FP16 online-attention development

The complete independently adapted source at `cases/native_fp16/kernel.hip`
keeps the tiled online algorithm, N=128, D=256, 32-thread blocks, both block
barriers per key tile, and two private running-state arrays per thread.
Inputs and outputs use FP16 storage; arithmetic, shared tiles and running state
use FP32. The group index flattens batch and attention head.

**This source has no whole-launch Lean certificate yet.** The accepted facts
below are source identity, address/ownership theorems, a sufficient footprint
condition and actual lane execution through the first block barrier. Whole-launch
execution, complete actual-trace membership and canonical-reference equality
must still be joined before this becomes an accepted source certificate.
It does not reproduce the authors' missing production adaptation or model run.

`native-provenance.json` records each independent source change. The first tile
initializes its maximum from its first score. Its previous maximum is then that
tile maximum and its previous denominator is zero, so the source avoids reading
uninitialized private state or multiplying zero by an overflowing exponential.
The output is zeroed by the kernel before any old-output read. Later key tiles
retain intermediate FP16 output rounding. No IEEE rewrite-equivalence or error
bound is asserted.

## Checked formal components

- `NativeAttentionProgram.lean` pins all 91 instructions, shared/local array sizes,
  native geometry and nine block phases. The permitted group count is
  `1 <= groups <= 65535`, with a proved global span below `2^31`.
- `NativeAttentionAddress.lean` proves bounded addresses, unique output owners,
  inverse coordinates covering every output slot, and actual machine location
  rules. It covers all permitted groups and row/column coordinates.
- `NativeAttentionFootprint.lean` proves that a trace satisfying the local access
  conditions passes the original machine's race check. Private arrays belong to
  their thread; Q/score rows have unique owners; K/V tile stores and reads must
  occur in opposite block-epoch parities. **The source's complete actual trace
  has not yet been proved to satisfy these conditions.**
- `NativeAttentionFirstLane.lean` now proves actual `runLane` execution through
  5,405 source instructions to PC 20, the first block barrier, for every permitted
  group count and arbitrary scalar operations. Every lane zeroes its 1,024 output
  elements, copies its first K/V rows, preserves inputs and produces a trace
  satisfying the footprint condition, assuming it starts with a good trace and
  an even block epoch. The [prefix checkpoint](PREFIX.md) does not yet compose
  the 32 lanes, resume the barrier or execute the attention compute stages.

Fresh checks accept the full source's IR and array layout and reject five
changes directly in Lean: a missing load barrier, a wrong tile-store owner,
a wrong running-state index, an omitted old denominator and a shrunken private
array. The last control preserves the instruction list and is refused by the
array-layout obligation. These are identity controls, not the paper's original
semantic mutation study. Small Lean witnesses also check the concrete conflict
before a block barrier and its absence after that barrier.

The address/footprint audits use only `propext` and `Quot.sound`; the execution
prefix also uses standard `Classical.choice` in some checked results. The source-binding
decision itself adds no axioms. The standalone component project rebuilds
outside the checkout using Lean 4.19.0; no Mathlib or model endpoint is needed.

```bash
lake -d lean build Lark.NativeAttentionAddress
python3 reproduction/online_attention/check_native_program.py --output /tmp/native-binding
python3 reproduction/online_attention/check_native_prefix.py --output /tmp/native-prefix
python3 -m unittest discover -s tests -p test_native_attention.py -v
```

The new reader is opt-in development code. The ordinary reader retains its
4,096-cell shared-array bound and refuses private array declarations. There is
no new verification CLI that could accept this source without its full proof.

## Finite access preflight

The full `[1,128,256]` source completed a value-erased preflight with 17,516,288
accesses and all 32,768 output slots initialized. It checked bounds, initialization,
barrier convergence and the footprint predicate for each access. All threads
halted after eight block-barrier resumes. Three variants were refused: a missing
load barrier, a wrong shared writer and missing output initialization.

This is an untrusted finite check without tensor values. It does not establish
universal execution or trace erasure. Its value and pairwise race-check APIs
refuse to return unavailable results; it exposes only initialized-slot counts
and streamed access statistics.

```bash
python3 reproduction/online_attention/check_native_accesses.py --output /tmp/native-accesses
```

## Separate native numerical checks

Both MI350X hosts passed 12 paired trials at one and three groups, always with
128×256 inputs per group. Six finite families include sharp distributions and
common score shifts above 2,000. Every trial runs this FP16 adaptation and the
unchanged extracted upstream FP32 kernel on exactly promoted inputs.

The independent CPU audit recomputed all 12 float64 attention references and
checked both methods on both hosts: **3,145,728 comparisons, zero tolerance
failures**. The FP16 adaptation uses `0.002 + 0.002 * abs(reference)`; the FP32
baseline uses `0.0001 + 0.0002 * abs(reference)`. Maximum absolute errors were
`0.0015283703669408677` and `0.000020183673658247248`, respectively.

Each method's output stream is identical between the two hosts. Within each
host, 260,402 of 786,432 adapted half values differ in bits from the rounded
FP32 baseline. Intermediate half rounding is retained; the paths are not
claimed bit-equivalent. These finite results are not a numerical error theorem.

All allocation guards and read-only inputs passed runtime checks. The runtime
also checked the FP32 baseline's final denominator/max arrays; native private
accumulator streams were not exported. Compiler-reported inputs are captured
and hashed: 320 files on `mi350`, 315 on `mi350-2`.

```bash
python3 reproduction/online_attention/prepare_native_gpu.py --output /tmp/native-input
# Copy the frozen directory to each free GPU host, then run there:
HIP_VISIBLE_DEVICES=0 python3 /tmp/native-input/run_native_gpu.py \
  --input /tmp/native-input --output /tmp/native-device
# Retrieve both host directories, then audit on a CPU machine:
python3 reproduction/online_attention/audit_native_gpu.py --input /tmp/native-input \
  --host /tmp/native-mi350 --host /tmp/native-mi350-2 --output /tmp/native-audit.json
python3 reproduction/online_attention/check_native_gpu_controls.py --input /tmp/native-input \
  --host /tmp/native-mi350 --output /tmp/native-controls
```

The final command rejects fully rehashed claims of source certification or
original-paper completion, and a nonfinite adapted output. The
[frozen packet](results/native-fp16-v1/report.json) keeps the proof components,
preflight and hardware evidence separate. The earlier FP32-only packet remains
unchanged. No model calls, original H100 timings or new accepted source
certificates are included.
