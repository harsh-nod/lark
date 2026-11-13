# Benchmark-reference numerical audit

**The original paper is not fully reproduced.** This CPU protocol validates the
repository's independently reconstructed mathematical references. It adds no
kernel certificate, GPU trial, model call, IEEE equivalence theorem or
floating-point error bound. Publication and a complete frozen measurement from
these sources are pending.

The complete protocol covers all seventeen benchmark families at their existing
HIP-case shapes. Four input strata and five output positions give 340 sampled
final-output comparisons. It additionally checks every materialized attention
score: 65,536 dense-attention scores and 524,288 GQA scores across the four strata.
These are protocol sizes, not a claim that a published result packet already
exists.

The SDK validates each owned source, task and Torch reference, then renders its
actual polymorphic `LarkCertificate.spec`. The auditor checks the full reference
signature and its declaration ownership before unfolding it. It records the
corresponding elaborated `List Real` expression, and instantiates the same
generic reference with checked Float64 operations. Bounds errors, non-finite
arithmetic, zero denominators, unsafe declarations and unsupported computational
constructs cause a named refusal.

Storage conversions are identities in this idealization. The expected-value
track runs the unchanged owned Torch reference in Float64 with the same identity
storage conversions. Actual-dtype Torch values are reported separately. Passing
the idealized comparison establishes no equality or error bound for rounded GPU
arithmetic. The absolute and relative tolerances are each `1e-10`.

Attention reuses complete score tensors computed by the actual source
`scoreValue` function. It expands the existing `valueInput`, `probability` and
`softInput` definitions and substitutes a checked lookup only when the complete
source-call prefix matches. No score formula or buffer-wiring formula is copied.
The evidence retains the original and compiled scalar expressions and every
cached Float64 bit pattern. A Tensor subclass records the actual input of the
unchanged Torch reference's `softmax` call; the runner also checks that this
telemetry preserves the final reference outputs.

The separate guarded real-expression interpreter is retained for overlap checks.
Its explicit continuation machine uses bounded execution chunks and preserves
the original heartbeat context. It provides numerical evidence, not a universal
interpreter-equivalence theorem.

Use Lean 4.19.0, CPU PyTorch and the pinned, initialized Mathlib dependencies
described in the [production numerical-audit instructions](../specification_validation/README.md).
The runner compiles both numerical modules afresh and reuses only source-checked
SDK import caches.

```sh
LARK_REAL_PROJECT=/path/to/initialized/lean-real \
python3 reproduction/benchmark_specification_validation/study.py \
  --lean /path/to/lean-4.19.0/bin/lean \
  --output /tmp/lark-benchmark-reference-study
```

For a short execution, append `--case relu --stratum dyadic`. A subset run is
labelled with its actual case and stratum selection. Output must be outside a Git
checkout and must not already exist.

The output contains a source-only snapshot, source and compiled-module bindings,
generated Mains, input bit patterns, logs, numerical results and control receipts.
`controls.py` exercises seventeen negative cases and a positive case.
`materialization_controls.py` exercises seven negative cases and preservation of
signed-zero bits. Each numerical Lean process has the existing 180-second limit;
every new Lean module and Main uses recursion depth 10,000 and two million
heartbeats. No stack, shape, proof-fuel or resource-limit increase is used.

The authors' original registry, formalizations, validation inputs, models, token
history and NVIDIA measurements remain separate unreproduced requirements.
