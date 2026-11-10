# Native RMSNorm work in progress

**No RMSNorm certificate has been exported by this extension.** The complete
source-to-launch and source-trace Lean proofs are still pending. The intended
phase value has a proved canonical-real bridge, and finite native GPU comparisons
have passed. Neither result certifies execution of the complete source program.

The current target is a weighted FP16 row of 16,384 elements, with eight-element
vector ownership and the native 1,024-thread/wave64 launch. It is an independent
adaptation of `csrc/layernorm_kernels.cu` at vLLM commit
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8`. This is the largest published
Level-1 normalization width, with the additional weight input of the production
function. It is not the authors' original production adaptation or model run.

The selected template is FP16, rank two, contiguous rows, one shared weight
vector and `HasWeight=true`. The host selects vector width eight and block size
1,024 at this width for fewer than 256 rows. The fixture pins those parameters,
epsilon `1e-5` and one row; the development task contract permits the same
launch organization at `1 <= rows < 256`. Ordinary 16-byte vector alignment is
an explicit host requirement.

The adaptation keeps half-to-float loads, FP32 accumulation, the weight
multiplication and the final half conversion. It scalarizes each eight-element
vector while preserving the ownership and traversal order. It makes the
two-stage block reduction explicit: sixteen wave64 partials go to shared
memory, a block barrier orders their reads, a logical 16-lane cohort reduces
them, and another block barrier orders the scale broadcast. CUB/rocPRIM's
architecture-specific reduction is represented by explicit guarded shuffle-down
steps. This is a chosen rewrite under intended real sum laws, not a proved
byte-for-byte inlining or a floating-point equivalence theorem for CUB.

The preprint's `app:library` describes template instantiation, helper inlining,
scalarized vector accesses, full-mask shuffle steps and an aligned-path
specialization among its adaptations. Its actual files/revisions remain
unavailable. Our source choices and departures are recorded independently in
`provenance.json`; they do not reconstruct the authors' eight rewrite steps.

The following proof foundations have been checked:

- `Lark.VectorStride` proves traversal coverage, inverse vector/thread/component
  coordinates, unique output ownership and signed-int32 address bounds.
- `Lark.ReductionFootprint` derives race freedom from local conditions on
  read-only global inputs, unique output writers, shared partial stores and
  barrier-separated reads/broadcasts. The kernel still has to prove those
  conditions for every actual access.
- `Lark.PartitionCollective` adds an opt-in scheduler for complete aligned
  logical partitions inside a physical wave64. It preserves memory, index
  registers, access traces and synchronization epochs across a shuffle. It
  rejects incomplete, duplicated, mixed-instruction or cross-wave cohorts.
  Earlier pinned machines are unchanged. Native RMSNorm trials exercise this
  logical-16 pattern, while the complete kernel simulation proof is pending.
- `Lark.NativeRmsNormProgram` fixes all 71 frontend instructions, the native
  geometry and the actual two block barriers. A source-binding check accepts
  the baseline and directly rejects four modified IR statements in Lean.
- `Lark.DownReduction` proves that the guarded ascending shuffle-down recurrence
  has a complete contiguous tree at lane zero, for arbitrary addition operations.
  It includes the out-of-range self-source behavior and proves exact leaf coverage.
- `Lark.NativeRmsNormValue` states the intended per-thread accumulation,
  wave/block reduction and weighted output expression. `LarkReal.NativeRmsNorm`
  proves that this value equals the canonical real sum-of-squares RMSNorm.
  **Equating actual execution to this value remains an open proof obligation.**

The [HIP shuffle documentation](https://rocm.docs.amd.com/projects/HIP/en/latest/how-to/hip_cpp_language_extensions.html#warp-shuffle-functions)
describes power-of-two logical subgroups and out-of-range up/down sources
returning the caller's value. The development model conservatively requires
whole aligned logical partitions; arbitrary sparse active masks are unsupported.

The development fixture has 71 instructions. Untrusted symbolic execution
completes with 66,593 accesses and 16,384 outputs. Every recorded access matches
the proposed footprint classification; polynomial preflight finds exactly one
square of each input in the reduction, and checks all output expression wiring.
Four source changes are refused by that preflight. Those preflight results are
separate from the four direct Lean program-identity rejections; neither is a
complete semantic mutant study or an original-paper mutant result.

```bash
python3 reproduction/production_rmsnorm/run_symbolic.py --output /tmp/lark-rms-preflight
python3 reproduction/production_rmsnorm/check_program.py --output /tmp/lark-rms-binding
python3 -m unittest discover -s tests -p test_partition_collective.py -v
```

The latter needs Lean/Lake 4.19.0 on `PATH`. It checks the Python scheduler and
development contract plus symbolic Lean cohort, footprint and concrete race
checks. These checks use the standard Lean axioms and need no Mathlib, GPU or
model endpoint. The algebra component uses the existing pinned Mathlib package:

```bash
cd lean-real
lake build LarkReal.NativeRmsNorm
```

`upstream/` captures the original entry, selected helpers and the installed
reduction headers from both hosts. Their ROCm versions are 7.2.1 and 7.3.0;
eleven of the twelve selected headers match, while the DPP header differs.
These are selected source captures. The separate [native validation packet](RESULTS.md)
also captures and hashes every compiler-reported input for each actual comparison
build (620 files on `mi350`, 616 on `mi350-2`). Both hosts passed 24 trials at
1, 3, 64 and 255 rows, totaling 127,008,768 CPU-reference comparisons. There are
signed-zero and one-half-ULP differences; bit identity is not claimed.
