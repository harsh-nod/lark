# Native llm.c softmax source study

This independent AMD adaptation retains all three passes of llm.c
`softmax_forward_kernel7`: maximum, exponentiation/sum and normalization. It
implements both the clamped-read original and the guarded-read repair described
in [Appendix A.14 of the paper](https://arxiv.org/html/2611.02028v1#A1.SS14).
The complete sources are bound to their translated programs. Instruction-level
Lean witnesses and complete finite address traces expose the original conflict;
finite numerical tests pass on both AMD hosts. Whole-source reachability,
universal repaired-launch correctness and its reference bridge remain open.
**This development profile issues zero source certificates.**

## Source and supported launch

[Provenance](provenance.json) pins
[llm.c commit f1e2ace](https://github.com/karpathy/llm.c/blob/f1e2ace651495b74ae22d45d1723443fd00ecd3a/dev/cuda/softmax_forward.cu).
The upstream source, `common.h` and MIT license are retained in [upstream/](upstream/).
The Git blob's raw SHA256 is
`5bc29aae3b655fbccdb40a9dc3a071e64f9b9f53e2c98d0fb0c82e346990013e`.
The earlier race-excerpt study recorded a full-source hash after adding one
trailing newline; the new provenance records both representations explicitly.
This pin identifies independently selected public source, not the authors'
unreleased adapted kernel or exact experiment revision.

The closed launch has FP16 contiguous, mutually disjoint input/output buffers
of shape `[rows,50257]`, 1,024 threads per block and one block per row. Physical
wave64 contains two complete logical32 groups. Positive row counts must satisfy
`rows * 50257 < 2^31`, so the maximum is 42,730 and the upstream default of
8,192 rows is included. The signed bound applies to addresses actually computed
after the source's clamp or bounds guard.

[Rewrites](rewrites.json) distinguish scalarization/translation from semantic
departures. Input and output storage are changed from upstream FP32 to FP16,
as in the paper's stated adaptation. The source keeps unrounded FP32 sums,
FP16 exponentials in output, both separate eight-element private arrays and all
four block barriers. The maximum reduction uses logical32 **down** shuffles;
the sum uses logical32 **XOR** shuffles. The repair bounds the normalization
load and removes its clamp; the two separate load/store loops remain.

The opt-in [reader](../../lark_kernels/native_softmax.py) handles this closed
source family with unchanged machine definitions and fuel `(4096,8,5,1)`.
It gives each private-array cell its actual thread owner. A dedicated reserved
`-INFINITY` spelling maps to an abstract seed operation; no rational, real or
IEEE interpretation of that marker is asserted. Ordinary task parsing and
registered certificate profiles are unchanged. The secondary 32-thread witness
described by the paper is outside this 1,024-thread study.

## Checked proof scope

The latest [component packet](results/components-v2/results.json) freshly builds
eight Lean modules, audits 48 declarations and rejects nine false claims.
Its [archive replay](results/components-validation-v2/results.json) repeats the
reader check, build and refusals with Git unavailable and no own compiled Lean
cache. It also reproduces the full finite traces from frozen source. Earlier
`components-v1` packets retain their original narrower row bound.

The four local proof files establish:

- Exact full-program/interface binding: 117 original instructions and 116 repaired
  instructions, with the pinned source, layout, geometry and fuel.
- Column coverage, ownership, address bounds and injectivity.
- A sufficient access classification that implies race freedom.
- Actual single-instruction reader/writer traces from explicit intermediate
  states, their conflicting pair and the repaired guard's skipped load.

The Lean instruction witnesses use arbitrary arithmetic operations and values.
They do **not** prove that the initializer reaches those intermediate states.
Likewise, the sufficient classification theorem does not prove that every access
in every complete repaired launch satisfies the classification. Those are
separate remaining source-execution obligations. There is no canonical-real
softmax theorem, IEEE equivalence theorem or numerical error bound here.

The separate [finite source replay](results/finite-trace-v1/results.json) erases
scalar values and executes integer control, source accesses, barriers and
logical collectives for one complete 1,024-thread block:

| Variant | Access records | Classification failures | Final epoch | All threads halt |
| --- | ---: | ---: | ---: | --- |
| Original | 489,926 | 7,081 | 4 | Yes, PC116 |
| Repaired | 475,752 | 0 | 4 | Yes, PC115 |

The canonical conflict is thread0's normalization read at PC102/event273898 and
thread80's write at PC111/event290953. Both access output cell50256 in block
epoch4. The reader's unclamped column51200 is out of bounds, then clamps to50256.
The repair's guard skips that read. The replay preserves every address record
in compressed streams; the independent archive replay compares their complete
decompressed SHA256 hashes and diagnostic records. This finite replay is not a
universal Lean execution theorem or a numerical run.

```bash
# Lean 4.19.0, standard library only; use fresh output directories.
python3 reproduction/production_softmax/check_program.py --output /tmp/softmax-components
python3 reproduction/production_softmax/replay_components.py \
  --packet /tmp/softmax-components \
  --finite-trace-packet reproduction/production_softmax/results/finite-trace-v1 \
  --output /tmp/softmax-components-replay --lean-bin /path/to/lean-4.19.0/bin
python3 -m unittest discover -s tests -p test_native_softmax.py -v
```

## Finite AMD numerical evidence

Each host ran both full native sources for 24 paired trials: rows1,3,64,255
times six input families. The families cover seeded normal values, signed zeros,
constant negative values, structured dyadics, a final-cell maximum and wide
alternating values. Each kernel is included verbatim in the HIP driver under an
entry-symbol-only rename. The driver records compiler dependencies, allocation
guards and read-only input preservation. It does not assert that executing the
original source on hardware was race-free.

| Host | Trials / launches | FP64-reference comparisons, both variants | Tolerance failures |
| --- | ---: | ---: | ---: |
| mi350 | 24 / 48 | 194,796,132 | 0 |
| mi350-2 | 24 / 48 | 194,796,132 | 0 |

Tolerance is `2^-24 + 0.002 * abs(reference)`. The four actual output streams
are byte-identical, even though the original has the source-level conflict.
An independent CPU check reproduces the NumPy FP64 stable-softmax formula with
Torch FP64, then checks all stored FP16 reference bits. A further direct check
compares every actual GPU output against the declared
`torch.softmax(inp.float(), dim=1).half()` reference. That also has zero tolerance
failures; it has 937,383 differing FP16 values and maximum absolute error
`1.52587890625e-05`, so this is not bitwise equivalence to the reference.
Byte-identical streams are checked once per SHA256 and mapped explicitly to all
four host/method names.

The upstream-default dataset has 8,192 rows and 411,705,344 values per method.
Its generator copies the pinned `common.h` random helper bodies, uses
`srand(0)` and the original three-outlier loop, which **multiplies by20** before
the documented FP16 conversion. The generator records its C compiler, libc,
precursor hashes and exact helper bytes. Its CPU reference checks have passed;
full-size GPU evidence will be recorded separately once completed.

Large raw input/output payloads are published as separate release assets;
metadata packets retain the original manifests and compiler inputs. The
[restorer](restore_gpu.py) reconstructs all original input and device streams
losslessly and checks each original manifest before independent numerical audit.
Release receipts and packet links are added after publication. No paid endpoints
or model calls are used. Original NVIDIA results, historical agent runs/token
costs and the authors' unreleased adaptation remain unreproduced.

```bash
python3 reproduction/production_softmax/prepare_gpu.py --output /tmp/softmax-input
python3 reproduction/production_softmax/prepare_upstream_gpu.py --output /tmp/softmax-upstream-input
# Copy one prepared directory to each available AMD host, then run there:
python3 /tmp/softmax-input/run_gpu.py --input /tmp/softmax-input --output /tmp/softmax-device
# Retrieve the original device streams/manifests, then audit on a CPU with NumPy:
python3 reproduction/production_softmax/audit_gpu.py --input /tmp/softmax-input \
  --device-output /tmp/softmax-device --output /tmp/softmax-audit
python3 reproduction/production_softmax/audit_torch_gpu.py --input /tmp/softmax-input \
  --mi350 /tmp/softmax-mi350 --mi350-2 /tmp/softmax-mi350-2 --output /tmp/softmax-torch-audit
```
