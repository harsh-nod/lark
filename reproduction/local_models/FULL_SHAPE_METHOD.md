# Full-size model proof-task preparation

This prepares an independent experiment at all seventeen existing HIP benchmark
shapes. **No new model inference has run.** The earlier three-model cohorts used
reduced fixtures and a different three-slot protocol; their pass rates and token
counts must remain separate. Neither experiment recovers the paper's original
kernels, proof-agent harness or historical model outcomes.

`full_shape.py` validates each owned source/reference/task through its actual SDK
backend and retains the generated fixed declarations. Models will supply four
tactic bodies: source/program binding, complete execution, race freedom and
output/reference equivalence. The remaining certificate statements and assembly
are fixed. This is a fixed symbolic scaffold; it does not measure agent-generated
segmentation or reproduce the paper's original stage costs.

The preparation supplies existing owned proof libraries through source-checked
imports. Every newly generated Main uses recursion depth 10,000, two million
heartbeats and a 180-second process limit. Existing library sources retain their
original settings. The source-checked import build retains its 600-second limit;
its caches may be reused. This is not a cold rebuild of all dependencies.

```bash
LARK_REAL_PROJECT=/path/to/configured/lean-real \
python3 reproduction/local_models/full_shape.py \
  --lean /path/to/lean-4.19.0/bin/lean \
  --output /tmp/lark-full-shape-model-preparation
```

Outputs must be fresh and outside Git. The source snapshot records the SDK,
reference libraries, task bytes and preparation driver. The preparation runs
each SDK proof as a positive control, then rejects the same task with all four
proofs replaced by `by fail`. The seventeen positive and seventeen negative
checks passed. Seven additional syntax controls reject a missing/extra slot and
admission, resource overrides, unchecked evaluation, declarations and a non-proof
in the additional execution slot. All seventeen request files were separately
checked to contain four masked proofs and the fixed resource settings.

SDK tactic bodies are retained only in the control artifacts. Model-visible
requests contain the masked Main, theorem types, original kernel/reference/task
bytes and a library catalogue. A future inference controller must expose only
these requests and allowed library sources; it must not expose SDK renderer
implementations or positive-control solutions. No model success, source
certificate, GPU trial or new mathematical theorem is counted by preparation.
Candidate proofs will still require independent Lean checking and axiom audits.

The [preparation receipt](results/full-shape-preparation-v1/results.json) and
[frozen artifacts](results/full-shape-preparation-v1/preparation.tar.gz) retain
the complete controls, source manifest, generated requests and checker logs.
After extracting that archive to a fresh directory, repeat the request/slot checks:

```bash
python3 reproduction/local_models/results/full-shape-preparation-v1/controls.py \
  --repository . --prepared /tmp/extracted-preparation --output /tmp/slot-checks
```

The mathematical semantics use abstract scalar operations. Hardware correspondence
and floating-point behavior retain the existing studies' separate limits.
