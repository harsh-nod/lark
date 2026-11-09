# MI350X extension: nonlinear functions and explicit FP16 storage

This extends the independent reproduction with a separately pinned
[Lean model](../../lean/Lark/Nonlinear.lean), strict source/reference support for
nonlinear scalar operations, and explicit conversions between FP16 storage and
FP32 arithmetic. [RESULTS.md](RESULTS.md) records the measured outcomes and
[results/](results/) contains the raw artifacts.

This remains a partial, independent reproduction of
[LARK](https://arxiv.org/abs/2611.02028v1). The original registry, agent harness,
kernels and certificates were unavailable. No model calls are made.

## What changes

The new profile adds scalar division, exp, tanh, reciprocal square root,
`__half2float` and `__float2half`. Source buffers must match their declared
`float32` or `float16` type. Arithmetic on half values and implicit narrowing
are refused; kernels must convert half loads explicitly and convert values
before half stores. FP32 registers and shared arrays retain their previous form.

The independent reference reader adds explicit `.float()`/`.half()`, SiLU,
tanh-approximate GELU, stable Softmax, unweighted LayerNorm/RMSNorm with explicit
epsilon, mean/maximum reductions, transpose, selection, stacking and bounded
head repetition. Unknown options and namespaces remain refused.

`Nonlinear.lean` is a separate model and namespace. Model selection is derived
from the program, specification and declared buffer types, then checked on
replay. Old scalar-v1 certificates still use the original `Model.lean`; all 18
historical reproduction statements regenerate byte-for-byte.

**A certificate proves equality in the stated abstract operation model.** Its
scalar operations, including conversions, are universally quantified. This is
not a formal IEEE binary16 implementation or a numerical-error proof. The
source/reference mapping, operation-to-hardware interpretation, host allocation
contract and phase-reduction metatheory remain trusted. Finite hardware checks
are separate evidence and cannot replace those assumptions.

## Coverage and contracts

The generated cases include all 17 task families with reduced FP16 input/output
shapes, plus FP32 cases for the five previously unsupported Level-1 families.
The CPU run additionally checks CUDA launch profiles for FP16 ReLU, Softmax and
GEMM, and sends 28 independent mutants directly to Lean, bypassing Python's
preflight rejection. Six equivalent index-plus-zero controls must pass.

Convolutions retain the original small valid-padding fixtures. Norms use four
elements, no affine parameters and epsilon 1e-5. GELU uses the tanh approximation.
FFN/SwiGLU use two hidden elements and explicitly round their hidden activation
to FP16 before the second product. RoPE uses adjacent pairs and supplied tables.
Dense attention has two query/key positions and head dimension four. GQA uses
two query heads, one KV head, two positions and **head dimension one**. These
attention fixtures have no causal mask or dropout and do not implement the
FlashAttention algorithm. Scores are computed once per query row. These shapes
are deliberately small because proof reduction remains expensive.

There is no induction-based scalability result, original-size FP16 certificate,
PTX/tensor-core implementation, original mutation-set reproduction or model
pass-rate/token-cost study. CUDA profiles are checked on CPU, not NVIDIA hardware.

## Reproduce on CPU

From the repository root, with Python 3.11+ and Lean 4.19.0:

```bash
python3 -m pip install -e .
python3 reproduction/nonlinear/run_cpu.py --output /tmp/lark-nonlinear-cpu
python3 reproduction/nonlinear/make_calibration.py --output /tmp/lark-nonlinear-calibration
```

With CPU PyTorch installed, prepare independent expected outputs and compare the
reference AST against them:

```bash
python3 reproduction/nonlinear/prepare_gpu.py --output /tmp/lark-nonlinear-input
```

The data generator checks six seeded random trials and four probes for every
case. It compares the formalized expressions using explicit binary32 and
binary16 operations against CPU PyTorch, then stores the PyTorch results for
GPU checks. FP16 comparisons use rtol=atol=0.01; FP32 comparisons use
rtol=2e-5, atol=2e-6. The input/reference/wrapper hashes are recorded.

The CPU suite exports a complete standalone Lean certificate per baseline,
a source/theorem index, failed mutant statements/logs and positive controls.
Output directories must be new. `--lean /path/to/lean` selects the toolchain;
`--timeout` defaults to 180 seconds per Lean invocation. A certificate must
also pass a separate source-binding and Lean recheck. Unsupported programs,
failed proofs and timeouts cannot become verified results.

A [recorded Softmax certificate](results/softmax-certificate/) is directly
inspectable. All baseline proofs and rejected candidates are also retained in
`results/cpu-artifacts.tar.gz`. CPU source snapshots preserve the original run
and its completion scheduler; `results/device-source-bundle.tar.gz` preserves
the actual GPU runner, source/task/reference bytes, prepared inputs and index.
Later parser restrictions preserve every recorded fixed theorem statement.

If a stopped run already completed and rechecked every baseline, pending mutation
checks can be completed with four concurrent Lean processes:

```bash
python3 reproduction/nonlinear/finish_mutations.py --output /tmp/lark-nonlinear-cpu --jobs 4
```

This validates the cached artifacts and fixed statements, preserves completed
checks, and records the continuation source and concurrency. Baseline proofs are
reused; the continuation does not issue new baseline certificates. Run it only
after the original writer has stopped. Wall times from concurrent checks are
not controlled performance measurements.

## Execute on MI350X

The reduced-source/calibration runner needs only HIP and Python's standard
library on the GPU host. Copy its files, prepared inputs, calibration data and
certificate index to the host, preserving the relative location of
`run_gpu.py` and `probes.hip`:

```bash
HIP_VISIBLE_DEVICES=0 python3 reproduction/nonlinear/run_gpu.py \
  --input /tmp/lark-nonlinear-input \
  --certificate-index /tmp/lark-nonlinear-cpu/certificate-index.json \
  --calibration /tmp/lark-nonlinear-calibration/operands.json \
  --output /tmp/lark-nonlinear-device --arch gfx950
```

Before executing, the runner requires a verified index entry for every input
case and matches its source, reference and task hashes. It compiles the exact
source bytes in the generated HIP wrapper with FP contraction disabled, checks
all outputs and preserves every input byte. The GPU host does not itself
recheck Lean. Kernel numerical comparisons use the declared tolerances; the
conversion probes use exact bit comparisons.

Four new scalar operations are compared against actual Lean Float64 evaluations
rounded to FP32, with rtol=2e-6 and atol=1e-6. That Lean interpretation does not
instantiate binary16 conversion; its unused half functions are identity stubs.
Half conversion is tested separately against Python's IEEE `struct` oracle:
all 63,488 finite binary16 encodings, including signed zero and subnormals, are
decoded and round-tripped, followed by 7,168 finite binary32 inputs covering
seeded random words, halfway ties and adjacent values, overflow and underflow.
NaN/infinite input encodings are excluded. These samples are not a proof of
all binary32 conversion behavior or all execution modes.

The original large-workload runner also runs on MI350X with ROCm PyTorch:

```bash
HIP_VISIBLE_DEVICES=0 python3 reproduction/run_hip.py \
  --output /tmp/lark-mi350-large --torch-compile \
  --calibration reproduction/results/calibration/operands.json
```

That run uses all Table 9 workload dimensions, six random trials plus four
probes per workload, and seven-round graph/event timings against eager and
compiled references. The large kernels have no new Lean certificates.
The old MI300X protocol, mathematical contracts and baseline conversion costs
remain described in [the earlier methodology](../README.md).

MI350X measurements extend the study to gfx950. They do not reproduce the
paper's H100 or MI300X latency cells. No unsafe mutants are executed on hardware.
