# Reproduction without NVIDIA hardware

This page records the original scalar-v1 study. The later
[MI350X extension](nonlinear/README.md) adds nonlinear and explicit FP16-storage
proof support; its reduced certificates and measurements have a separate report.
Later [pointwise](pointwise/README.md) and [GEMV](reduction/README.md) studies add
full-size induction certificates and exact-source validation on two MI350X hosts.
The [coverage ledger](COVERAGE.md) tracks all paper results across these studies.

This is an **independent, partial reproduction** of
[LARK (arXiv:2611.02028v1)](https://arxiv.org/html/2611.02028v1).
The measured outcomes are in [RESULTS.md](RESULTS.md), with raw JSON, proof sources,
logs, and source snapshots in [results/](results/). No paid or hosted model calls
were made. CPU Lean checks and one AMD MI300X were used.

The paper's [arXiv source bundle inventory](results/paper-source-manifest.json)
contains its manuscript and figures, not the
KernelCraft registry, original kernels, proof-agent harness, or certificates.
We did not locate an authors' implementation at experiment time. Consequently,
these experiments test this repository's implementation. They do not recover the
paper's model pass rates, original benchmark latencies, or full production proofs.

## What is exercised

| Experiment | Implementation and scope |
| --- | --- |
| Level-1 proof coverage | Seven families at reduced float32 shapes: ReLU, GEMV, GEMM, batched matmul, linear, convolution, depthwise convolution. Each uses both CUDA and HIP launch profiles. |
| Mutation rejection | Four ReLU mutations and five GEMM mutations per language; five additional mutations of a shared-memory sum proxy per language. Every mutant reaches Lean, bypassing Python preflight. |
| Positive controls | Equivalent index-plus-zero rewrites for each mutation target/language. |
| Segmentation representation | Flat versus barrier-grouped syntax for the same GEMM, two runs each. This does not implement the paper's induction or LLM ablation. |
| Concrete-shape scaling | Two-output products with inner dimension 1, 2, 4, 8. Measures this bounded checker, not paper-scale proof generation. |
| Production bug witness | Lean checks the reported threads 0/80 and cell 50256 against a pinned upstream final-pass formula. A separate minimal repair is certified in both languages. |
| GPU functionality | Independent FP16 HIP programs at all 12 Level-1 and five Level-2 dimensions in Table 9, with six random trials plus four deterministic probes. |
| GPU latency | Seven rounds of HIP-event timings for our programs and same-contract eager/compiled PyTorch references. |
| Scalar calibration | 256 finite operand pairs each for add, subtract, multiply, maximum: actual Lean `applyBinary` Float64 evaluations, rounded to FP32, versus a compiled HIP kernel. |
| Certified-source GPU checks | The exact reduced float32 HIP source bytes used in nine certificates, ten trials each, with input preservation and exact output comparisons. |
| Reference translator | Optional exact-rational evaluation versus CPU PyTorch, including batch/spatial/grouped convolution and multidimensional broadcasting. |

The seven proof families are **7/12 task families, not 7/12 original paper
programs**. SiLU, GELU, Softmax, LayerNorm, and RMSNorm lack formal support in our
small scalar machine. Neither the large FP16 programs nor any Level-2 program
has a Lean certificate here. CUDA profiles are checked on CPU; only HIP is run
on hardware. There is no PTX implementation.

## Run on CPU

Use Python 3.11+ and the repository's pinned Lean 4.19.0. No GPU or model is needed:

```bash
python3 -m pip install -e .
python3 reproduction/run_cpu.py --output /tmp/lark-cpu
python3 reproduction/production_race.py --output /tmp/lark-race
python3 reproduction/make_calibration.py --output /tmp/lark-calibration
python3 -m unittest discover -s tests -v
```

Pass `--lean /path/to/lean` to these experiment scripts if needed. Output directories
must be new. The CPU suite exports standalone baseline certificates, every mutated
Lean statement and diagnostic, positive controls, scaling/grouping experiments,
and an incrementally saved `results.json`. Nonzero exit means an expected result
failed, a bad candidate was accepted, or an experiment timed out. `unproved` is
failure of the supplied proof attempt; it is not a proof that a program is wrong.

With an existing CPU PyTorch installation, also run:

```bash
python3 tools/check_torch.py
```

The generated fixtures are committed. `python3 reproduction/make_cases.py`
regenerates them; it should leave their source/reference/task bytes unchanged.

## Run on AMD

Use a working ROCm HIP compiler and a matching ROCm PyTorch environment. The
recorded run used gfx942, ROCm 7.2.4, Python 3.12.3, PyTorch 2.14.1+rocm7.2,
Triton 3.8.0, and NumPy 2.5.4. A fresh environment for that software combination:

```bash
python3 -m venv /tmp/lark-rocm
/tmp/lark-rocm/bin/pip install torch==2.14.1+rocm7.2 \
  --index-url https://download.pytorch.org/whl/rocm7.2
/tmp/lark-rocm/bin/pip install numpy==2.5.4
HIP_VISIBLE_DEVICES=0 /tmp/lark-rocm/bin/python reproduction/run_hip.py \
  --output /tmp/lark-amd --torch-compile \
  --calibration /tmp/lark-calibration/operands.json
HIP_VISIBLE_DEVICES=0 /tmp/lark-rocm/bin/python reproduction/run_certified.py \
  --output /tmp/lark-certified \
  --certificate-index reproduction/results/certificate-index.json
```

`--torch-compile` is optional and invokes local compilation, with no model calls.
The recorded certificate index binds the committed reduced HIP sources,
references and task files to the archived, checked proof sources. The GPU runner
checks these hashes before compilation; it does not recheck Lean on the GPU host.
The intentionally racy program is never executed on the GPU.

The large HIP kernels are simple independent implementations. GELU uses the tanh
approximation; norms have no affine parameters and epsilon 1e-5; convolutions use
valid padding, batch one, stride one; RoPE uses adjacent pairs and supplied tables;
FFN/SwiGLU store a FP16 intermediate and use two launches. The `flash_attn` workload
computes dense scaled dot-product attention and does not implement the
FlashAttention algorithm. GQA uses eight query heads, two KV heads, dimension 64,
and no causal mask. [catalog.py](catalog.py) and each JSON row declare the contracts;
these choices cannot be asserted equal to the unavailable registry.

Numerical comparisons use rtol=atol=0.01. Random inputs have normal standard
deviation 0.25. Probes are zero, constant 0.125, alternating +/-0.125, and small
uniform inputs. These do not establish numerical error bounds or edge-case
coverage. The scalar study excludes NaNs, infinities and subnormals, ignores the
sign of equal zeros, and uses Float64 then FP32 rounding. It does not formalize
IEEE arithmetic or test the complete machine.

Latency is the median of seven HIP-event rounds. Each timed graph contains 20
calls, after warmup; results are per call. This reduces Python/launch overhead
and is explicitly our protocol, since the paper's precise timing harness is
unavailable. Compilation/autotuning time is excluded. Compiled references use
`fullgraph=True, mode="max-autotune-no-cudagraphs"`; each receives a separate
specialization and one numerical comparison. Eager and compiled references
convert FP16 inputs to FP32 and outputs back to FP16. Their costs include those
conversions. This is not a fastest-vendor-library sweep. Several of our HIP
kernels are much slower than these baselines and the paper's reported kernels.

## Audit the recorded artifacts

```bash
mkdir /tmp/lark-recorded
tar -xzf reproduction/results/cpu-artifacts.tar.gz -C /tmp/lark-recorded
python3 -m lark_kernels check /tmp/lark-recorded/gemm-hip
lean reproduction/results/production-race/witness.lean
python3 reproduction/summarize.py
```

All baseline certificates contain a standalone `Main.lean` with the complete
machine model and theorem. Mutant directories contain their rejected statements
and logs, not certificates. The CPU source snapshot preserves the exact pre-format
experiment sources named by the recorded SHA-256 hashes. Current sources include
formatting, stricter rank validation for `bmm`, and updated scope text. These do
not change the generated baseline theorems; the machine model is unchanged.

The production witness uses a separately pinned public llm.c revision, with its
MIT license and provenance in [upstream/](upstream/). The paper's exact upstream
revision and FP16 adaptation were unavailable. Source-to-formula mapping is
inspected and trusted. The witness proves the conflicting access pair and that
moving the load inside its bounds guard removes that pair; it does not prove
whole-kernel correctness or the absence of every other race. The tiny fixed
reproducer has its own full certificate.

The main remaining requirements are the authors' registry/proof artifacts and
frontends for PTX, FP16, transcendentals, collectives and induction-based loop
proofs. NVIDIA hardware would enable H100 execution and timing, but its absence
does not itself prevent CPU Lean checking of a provided PTX certificate. Model
pass-rate, token-cost and LLM ablation studies are outside the offline/free run.
