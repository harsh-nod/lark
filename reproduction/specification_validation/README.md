# Numerical audit of elaborated Lean references

The completed [production study](RESULTS.md) matched **240 sampled values**
across twelve variants and four input strata. Its immutable
[source and evidence packet](results/production-real-v1/manifest.json) contains
712 owned source files and 240 evidence files inside two archives. All fourteen
numerical negative controls and all
[26 packet mutation controls](results/production-real-packet-controls-v1/results.json)
passed. A separate fresh numerical recomputation is in progress; it is not
counted as complete by these file-verification receipts.

The paper's Appendix A, “Kernel-independent trusted base,” tests its Torch
formalizations with a metaprogram that evaluates the **elaborated Lean
specification** in float64. GPU-versus-Torch tests alone do not exercise this
part of the trust boundary.

`SpecAudit.lean` implements an independent version of that numerical method.
It imports the existing reference definitions, elaborates their applications,
checks that their type is `List ℝ`, unfolds the imported definitions, and
interprets a closed set of mathematical operations and list constructs.
Unsupported constructs, invalid indices, non-finite values and unsupported
primitive instances must produce named refusals. It does not accept a Python
copy of the Lean reference as the value under test.

The production study covers ten mathematical reference families, with both
rotary layouts giving twelve variants. Softmax is included as a mathematical
reference; this does not certify the original racy kernel. Inputs use four
deterministic strata: dyadic values, seeded normal values, sparse basis values
including signed zero, and alternating values with small perturbations. Five
output indices are sampled at the existing case shapes. This is sampled
numerical evidence, not an exhaustive equality check.

The original owned `reference.py` files are executed unchanged on CPU. There
are two explicit Torch tracks:

- The float64 track interprets floating storage casts as identities, matching
  the existing exact-real Lean interpretation. It is compared against the
  metaprogram with absolute and relative tolerance `1e-10` each.
- The original-dtype track uses the task's actual FP16 inputs and reference
  casts. Its sampled differences from Lean float64 are reported separately.

Neither track proves IEEE equivalence or a floating-point error bound. The
auditor produces **zero certificates**, changes no certificate provider or
proof theorem, makes no model calls, and launches no GPU work. It does not
reproduce the authors' unavailable original Torch registry or validation data.

Use Python with CPU-capable PyTorch and the pinned Lean 4.19.0 toolchain. The
optional Mathlib dependency checkout must match `lean-real/lake-manifest.json`.
The SDK checks its nine dependency revisions and owned source/compiled import
hashes. It can reuse those checked imports; the numerical auditor itself is
compiled from frozen source for every run.

```bash
LARK_REAL_PROJECT=/path/to/initialized/lean-real \
python3 reproduction/specification_validation/study.py \
  --lean /path/to/lean-4.19.0/bin/lean --output /tmp/lark-spec-audit
```

The output directory must be new and outside Git. `--case` and `--stratum`
select diagnostic subsets. Results retain actual elaborated expressions,
float64 bit patterns, expanded-definition names, input/main/log hashes,
unchanged reference and task hashes, toolchain details, numerical controls,
and a runnable bundle of the owned source files. Managed compiled imports are
kept separately from that source bundle.

Every new Lean module and generated Main uses `maxRecDepth 10000` and
`maxHeartbeats 2000000`. Existing source kernels, proof fuel and shape bounds
are preserved. Failed development attempts are not successful study results.

Audit the published packet using Python's standard library, without executing
Lean, Torch, GPUs or models:

```bash
python3 reproduction/specification_validation/packet.py verify \
  --packet reproduction/specification_validation/results/production-real-v1 \
  --output /tmp/lark-spec-packet-verified
python3 reproduction/specification_validation/check_packet.py \
  --packet reproduction/specification_validation/results/production-real-v1 \
  --output /tmp/lark-spec-packet-controls
```

To recompute every sampled Lean and Torch value from the frozen owned sources,
compile the numerical auditor anew and reuse only imports checked by the pinned
SDK cache validator:

```bash
python3 reproduction/specification_validation/packet.py recompute \
  --packet reproduction/specification_validation/results/production-real-v1 \
  --output /tmp/lark-spec-recomputed --lean /path/to/lean-4.19.0/bin/lean \
  --dependency-project /path/to/initialized/lean-real
```

The packet preserves the exact source frozen at the start of measurement,
including the then-unused packet authoring helper. The top-level packet verifier
was subsequently tightened and tested. The reference, evaluator, inputs, raw
logs and numerical results remain unchanged. A fresh replay evaluates those
frozen references and evaluator, while the current verifier checks the resulting
scope and data. Existing checked reference-library imports may be reused;
this does not claim a cold rebuild of every imported proof or of Mathlib.
