# Multiwave scalar SiLU-and-mul

This independent study extends the [small upstream-derived adaptation](../production_activation/README.md)
to the public vLLM scalar fallback's native launch: `grid=tokens`,
`block=min(hidden,1024)`, and `idx += blockDim.x`. Lean proves the actual
hierarchical launch, including partial last warps, unequal strided-loop lengths,
every output and race freedom. The original paper's production sources and
outcomes remain unavailable. This is one function family at selected shapes.

| Case | Tokens | Hidden | Threads/block | HIP waves/block | Maximum loop iterations | Outputs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| full | 64 | 4097 | 1024 | 16 | 5 | 262,208 |
| tail | 33 | 1031 | 1024 | 16 | 2 | 34,023 |
| partial_wave | 7 | 65 | 65 | 2 | 1 | 455 |

The last case has one active lane in its final HIP wave. CUDA uses warp32 and
has three warps in that block. Widths not divisible by eight select the pinned
upstream scalar fallback for FP16. The packed vector branch remains unsupported.
Two additional HIP certificates cover symbolic extremes: one row with hidden
1,073,741,823, and 1,073,741,823 rows with hidden one. Those arrays were **not
allocated or executed**. Both input spans are 2,147,483,646 half cells.

The `silu-multiwave-v15` profile accepts a closed packed-row reference AST with
explicit FP32 computation and **intermediate FP16 rounding inside SiLU**, before
the gating multiply and final half conversion. Removing that rounding changes
529,104 outputs in the numerical dataset. The profile preserves all ten source
instructions, independently interprets the reference, and lifts its pointwise
expression to every row and column. Source/reference/task bytes and seven Lean
libraries are bound by `lark check`.

`ScalarLaunch.lean` proves a generic scheduler simulation against the unchanged
nonlinear machine. Its invariant-preservation and lane contract are discharged
by `Silu.lean`; neither output correctness nor race freedom is assumed. The
kernel theorem quantifies over every input, outside-memory function and abstract
operation interpretation. It uses only the printed standard axioms. Hardware
correspondence, the source reader, closed reference interpretation and external
phase-reduction metatheory remain trusted. There is no IEEE theorem or formal
equivalence proof of the upstream-to-adapted source rewrite.

[Results](RESULTS.md) contain the counts and limitations.
[Provenance](provenance.json) pins vLLM commit
`83f5de466a889c29ac5fbfbe342d6fe4c09811e8` and records every departure.
The unchanged upstream translation unit, licenses and eight pinned PyTorch Half
headers are reused from [the earlier archive](../production_activation/upstream/).
The extracted upstream comparison uses its actual `torch::headeronly::Half`
carrier. It does not require a PyTorch runtime on the GPU host.

Run a single source-bound certificate with Lean 4.19.0:

```bash
lark verify-silu reproduction/production_silu/cases/full/kernel.cu \
  --reference reproduction/production_silu/cases/full/reference.py \
  --task reproduction/production_silu/cases/full/task.json \
  --output /tmp/lark-silu-certificate
lark check /tmp/lark-silu-certificate
```

Freeze and rerun all eight certificates, independent rechecks and five direct
Lean controls:

```bash
python3 reproduction/production_silu/run_cpu.py \
  --output /tmp/lark-silu-cpu --lean /path/to/lean
python3 reproduction/production_silu/prepare_gpu.py \
  --cpu /tmp/lark-silu-cpu/cpu --output /tmp/lark-silu-input
```

The preparation uses CPU PyTorch and NumPy; exact recorded-input regeneration
requires PyTorch 2.11.0+cu130 and NumPy 2.4.4. Copy the resulting input directory
and frozen `run_gpu.py` to an idle MI350X, then run with the chosen device:

```bash
ROCR_VISIBLE_DEVICES=0 python3 reproduction/production_silu/run_gpu.py \
  --input /tmp/lark-silu-input --output /tmp/lark-silu-gpu
```

The GPU runner checks hashes, native warp width, block capacity and at least 98%
free device memory. It compiles the exact certified source and extracted
upstream scalar path for gfx950, disables contraction, and compares both with
CPU references. It checks every input byte and 128-byte guards around all three
allocations. These finite tests do not discharge Lean goals.

Audit the published evidence without new Lean, GPU or model execution:

```bash
python3 reproduction/production_silu/summarize.py --output /tmp/lark-silu-audit.json
```

The auditor checks archives, replays statement generation from the frozen
implementation, regenerates every dataset/driver/header byte and checks both
raw output streams independently of reported success. All model calls are zero.
CUDA evidence is CPU Lean checking only. This study is separate from the
seventeen-family full-shape ledger and does not change its trial counts.
