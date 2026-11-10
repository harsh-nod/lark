# Native RMSNorm development validation

**Zero RMSNorm certificates. The complete source execution and trace proofs are pending.**
These are independent measurements of the development adaptation, not recovered
paper experiments or a certificate for the complete upstream API.

The fixed profile is weighted FP16 RMSNorm at width 16,384, epsilon `1e-5`,
eight-element vector ownership and a native 1,024-thread/wave64 block. Each host
ran six finite input families at 1, 3, 64 and 255 rows. Each trial launched both
the unchanged adapted source and the selected original vLLM template. The
comparison retains the actual PyTorch Half carrier, vector reader and installed
hipCUB/rocPRIM reduction. Selected definitions are extracted byte-for-byte from
the pinned sources; unrelated translation-unit context is omitted.

| Measurement | mi350 | mi350-2 |
| --- | ---: | ---: |
| GPU | MI350X | MI350X |
| ROCm | 7.2.1 | 7.3.0 |
| Trials / launches | 24 / 48 | 24 / 48 |
| Adapted/upstream output pairs | 31,752,192 | 31,752,192 |
| CPU-reference comparisons | 63,504,384 | 63,504,384 |
| Numerical tolerance failures | 0 | 0 |
| Maximum absolute error against CPU | 0.00390625 | 0.00390625 |
| Adapted/upstream differing bit patterns | 3,631,665 | 3,631,665 |
| Differences consisting of signed zero | 3,631,444 | 3,631,444 |
| Nonzero differences / largest half ULP distance | 221 / 1 | 221 / 1 |
| Compiler-reported inputs captured | 620 | 616 |

The declared tolerance is `abs(actual - expected) <= 0.002 + 0.002 * abs(expected)`.
All allocation guards, inputs and weights remained unchanged. Each run required
at least 98% free memory on its selected GPU. The input families include seeded
normal values, zeros, a constant, structured dyadics, half-format corner values
and mixed magnitudes. No model calls or timings of the original H100 experiments
are included.

The standard-library raw-stream auditor independently recomputes the measurements
from the frozen inputs and both GPU output streams. A changed output is rejected
even after its stream hash, report hash and result manifest are refreshed. CPU
source-tree evaluation itself differs from the original PyTorch reference in
130 bits; upstream GPU differs from PyTorch in 294 bits on each host. Reduction
order and conversion behavior are not asserted to be bit-equivalent.

The Lean components prove vector ownership/bounds, race freedom from a local
access classification, complete-partition shuffle properties, the fixed IR
binding, guarded reduction tree coverage and the intended value's canonical-real
formula. The actual source must still be proved to complete, satisfy that access
classification and produce that value for every input and allowed outside state.
The four direct Lean controls reject program identity changes, not entire
semantic kernel correctness statements.

The subsequent [execution prefix](../../lean/Lark/NativeRmsNormPrefix.lean)
proves that the actual scalar source instructions execute for every allowed
thread, input and initial outside state, stopping at the first shuffle (PC 18)
within the declared lane fuel. It proves the ordered 16-term value in register
0, native row/lane/warp indices, unchanged memory and synchronization epochs,
preservation of other threads, and classification of every prefix access as an
input read. The proof uses the original two vector iterations and eight-component
inner loop, with 115 scalar instructions per thread. This is a component of the
pending whole-launch proof and adds no RMSNorm certificate.

The [cohort execution components](../../lean/Lark/NativeRmsNormFirstStage.lean)
then compose the sequential prefix lane fold with the first actual native-wave
shuffle and guarded scalar fold. Further components prove source-bound snapshot
transport for complete 64-lane and logical-16 cohorts, the intermediate source
stages (five native-wave stages and three logical-16 stages), their exact guarded
value recurrence, and preservation of inactive threads, memory, indices, epochs
and traces. The physical wave64 geometry remains fixed. At that checkpoint the
final shared-store steps, barriers, output phase and full scheduler composition
remained pending. `results/execution-stage-v1/` records their local checks;
its prefix CI receipt refers specifically to the earlier prefix commit.

The [native-wave tail](../../lean/Lark/NativeRmsNormLastWave.lean) now executes
the sixth source shuffle and the actual 64-lane final fold, including the guarded
addition, lane-zero shared store and scheduler convergence at the first block
barrier. It proves the exact stored partial, preservation of read-only inputs
and synchronization epochs, and classification of the new store in block epoch
zero. The full six-stage wave, 16-wave block, barrier-resume and output phases
still need composition. `results/execution-tail-v1/` freezes these checks and a
source archive rebuilt outside the checkout. This remains zero certificates.

The [first-block composition](../../lean/Lark/NativeRmsNormFirstBlock.lean)
now proves the actual first warp fold in the block scheduler for every input and
initial outside memory. All 16 physical wave64 groups execute the prefix and
six shuffle stages within the declared fuel. All 1,024 threads reach PC 38 with
their native indices, and every shared partial equals the intended `warpSum`.
The phase preserves read-only inputs and synchronization epochs and proves race
freedom of its complete actual trace. Earlier waves' partials remain intact.
`results/execution-block-v1/` freezes this checkpoint. The barrier resumes,
logical-16 scale reduction, output phase and whole-launch theorem are still
pending; the certificate count remains zero.

The subsequent [scale-entry components](../../lean/Lark/NativeRmsNormMixedStage.lean)
prove the actual first barrier resume, current block epochs advancing from zero
to one, and the sequential physical-wave entry fold. Exactly sixteen threads
load the proved shared partials; all other threads park at the actual second
barrier. The scheduler selects the complete logical-16 cohort from the physical
wave64, and the intermediate logical stages execute with their original physical
lane-fold order and unchanged inactive lanes. `results/execution-mid-v1/` freezes
these component checks. The final scale store, second barrier, output phase and
whole-launch theorem remain pending, with zero certificates.

The [complete middle block phase](../../lean/Lark/NativeRmsNormScaleBlock.lean)
now executes all four logical-16 stages inside the original physical wave64,
the exact source scale expression and the thread-zero shared store. It composes
the fifteen remaining physical waves, each taking its inactive source branch,
and proves all 1,024 threads converge at PC 55. The stored scale equals the
intended `scale`; global inputs, native indices and current epochs are preserved,
and the actual phase trace satisfies the race-freedom classification. The
[second barrier resume](../../lean/Lark/NativeRmsNormOutBarrier.lean) then advances
all participating threads to PC 56 and block epoch two. Both source block phases
compose from the initial state for every allowed row, input and outside memory.
`results/execution-scale-v1/` freezes this checkpoint. Output execution and
whole-launch correctness remain pending, with zero RMSNorm certificates.

`results/v2/` freezes the sources, generated data, host archives, raw audits,
component proof logs and controls. Its source archive can be extracted outside
the checkout. Extract `gpu-input.tar.gz` and either host archive into separate
directories, then run:

```bash
python3 reproduction/production_rmsnorm/audit_gpu.py \
  --input /tmp/rms-data/input --results /tmp/rms-host/results --output /tmp/rms-audit.json
python3 reproduction/production_rmsnorm/check_audit_control.py \
  --input /tmp/rms-data/input --results /tmp/rms-host/results --output /tmp/rms-control.json
```

These audits need Python 3 and the frozen packet, with no GPU, model endpoint,
Lean installation or network access. Native reruns use `prepare_gpu.py` and
`run_gpu.py`; CPU data generation needs the recorded PyTorch/NumPy environment.
