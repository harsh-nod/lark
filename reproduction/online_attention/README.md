# Online attention: value recurrence

Lean proves the normalized online update used by the pinned
[flash-attention-minimal kernel](https://github.com/tspeterkim/flash-attention-minimal/blob/00f8f46712d493665c900c32fa3a261c8ef3e20c/flash.cu).
This closes an algebra gap between the existing dense SDPA reference and a tiled
online algorithm. **It is not a whole-kernel certificate.** GPU execution,
source lowering, memory footprints and race freedom remain to be proved.

`LarkReal.OnlineSoftmax.run_reference` covers arbitrary real scores and signed
value vectors, arbitrary finite tile lengths and every output column. The first
tile must be nonempty; subsequent tiles may be empty. It proves equality to the
independent dense expression `sum(exp(score) * value) / sum(exp(score))`.
The invariant proves a positive denominator at every update, not just a
totalized equality that could hide division by zero.

The recurrence retains the source's expression order:

```text
m_new = max(m_old, m_tile)
l_new = exp(m_old - m_new) * l_old + exp(m_tile - m_new) * l_tile
O_new = (1 / l_new) *
        (l_old * exp(m_old - m_new) * O_old + exp(m_tile - m_new) * tile_pv)
```

The theorem initializes from the finite maximum of a nonempty first tile.
It does not model the upstream `-INFINITY` sentinel or prove that its first
iteration refines this initialization. It does not prove IEEE equivalence,
stability or a numerical error bound. The paper's own adapted FP16 kernel,
model run and measurements remain unavailable.

`upstream/flash.cu` and its Apache-2.0 license are captured unchanged from commit
`00f8f46712d493665c900c32fa3a261c8ef3e20c`; their hashes and the exact scope are
recorded in [provenance.json](provenance.json). This is the repository cited by
the manuscript's `flashattnmin` reference, not an inferred replacement library.

Initialize the pinned `lean-real` dependencies/cache, then run:

```bash
python3 reproduction/online_attention/run_algebra.py --output /tmp/lark-online-algebra
```

`LARK_REAL_PROJECT` can select an initialized optional-dependency checkout.
The runner verifies all nine dependency revisions and tracked source files,
builds the module in a source-checked managed cache, freshly rechecks its source
and audits nine theorems. Only `propext`, `Classical.choice` and `Quot.sound`
occur in the audits. There are no model calls.

One numerical Lean control accepts the correct update. Four false algebra
assertions are rejected: an omitted old mass, an omitted tile mass, a doubled
tile value and a reversed exponential rescale sign. Lean also proves an explicit
counterexample to each false assertion. These are independent algebra controls,
not source-kernel mutations or the paper's original mutation experiment.

The [recorded algebra packet](results/algebra-v1/results.json) contains the fresh
check, all controls, source hashes and logs. It adds zero source certificates
and zero GPU trials. Its standalone project also rebuilt outside the checkout;
the wheel contains the identical proof source.

## Separate native numerical experiment

The [native packet](results/native-v1/audit.json) runs the unchanged extracted
upstream FP32 `forward_kernel` on both `mi350` and `mi350-2`. Each host passed
24 cases and 374,784 output comparisons against freshly recomputed CPU Torch
float64 attention: **749,568 total comparisons, zero tolerance failures** at
`1e-4 + 2e-4 * abs(reference)`. Maximum absolute error was
`1.5769493966671932e-5`; both hosts produced identical output bytes.

Four shapes cover `(batch, heads, sequence, head dimension)` of `(1,1,32,32)`,
`(1,1,64,64)`, `(1,1,128,256)` and `(2,3,64,64)`. The third uses the published
Level-2 attention dimensions. Six finite input families include signed values,
uniform attention, sharp distributions and common score shifts exceeding 2,000.
The inputs are half-representable values stored in FP32 buffers. Output and
accumulator storage remain FP32. **This is not the paper's FP16-storage rewrite.**

Both devices report 160 KiB shared memory per block; the original 32×32 tile
needs 100 KiB at head width 256. The wrapper retains that tile and the complete
batch/head grid. It enables the requested dynamic shared-memory size, replaces
the Torch host launcher and initializes `O/l/m` as upstream's host does. Sequence
lengths must be divisible by 32 because the captured kernel has no tail guards.
The source's `-INFINITY` initialization executes on hardware here, separately
from the finite first-tile initialization of the mathematical theorem.

Each host ran 24 forward launches and 24 explicit maximum-initialization
launches, plus the wrapper's memory-zero operations. The runtime checked every
allocation guard, all read-only inputs, and the final denominators and maxima.
The offline audit independently rechecks output streams and recomputes all 24
CPU references; accumulator streams were not retained for independent rechecks.
Compiler-reported inputs are captured and hash-checked: 316 files on `mi350`,
311 on `mi350-2`. No performance measurement is claimed.

```bash
python3 reproduction/online_attention/prepare_gpu.py --output /tmp/online-input
# Copy that frozen directory to a free MI350 device, then run there:
HIP_VISIBLE_DEVICES=0 python3 /tmp/online-input/run_gpu.py \
  --input /tmp/online-input --output /tmp/online-device
# Retrieve each host's result directory, then audit on a CPU machine:
python3 reproduction/online_attention/audit_gpu.py --input /tmp/online-input \
  --host /tmp/online-mi350 --host /tmp/online-mi350-2 --output /tmp/online-audit.json
python3 reproduction/online_attention/check_gpu_controls.py --input /tmp/online-input \
  --host /tmp/online-mi350 --output /tmp/online-controls
```

The last command accepts a positive replay and rejects two fully rehashed
controls: a false original-paper completion claim and a nonfinite output.
The native experiment adds zero Lean source certificates and zero model calls.
Connecting the source's actual tiled launch and race freedom to the value
invariant, and then the paper's recorded departures, remains work.
