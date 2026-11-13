# Full-size offline model protocol

This prepares and runs an independent experiment at all seventeen existing HIP benchmark
shapes. The preparation controls make no model calls. The earlier three-model cohorts used
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
checks passed. Nine additional policy controls reject a missing/extra slot and
admission, resource overrides, unchecked evaluation, declarations and a non-proof
in the additional execution slot, including command/elaborator executors. All seventeen request files were separately
checked to contain four masked proofs and the fixed resource settings.

SDK tactic bodies are retained only in the control artifacts. Model-visible
requests contain the masked Main, theorem types, original kernel/reference/task
bytes and a library catalogue. A future inference controller must expose only
these requests and allowed library sources; it must not expose SDK renderer
implementations or positive-control solutions. No model success, source
certificate, GPU trial or new mathematical theorem is counted by preparation.
Candidate proofs require an exact term-parse check, Lean checking and axiom audits.
The shared parser reads proof strings as JSON data and requires a single complete
`by` term. Trailing commands are rejected before candidate elaboration. The SDK's
ordinary verification/recheck API and the earlier local-model runner use this
boundary too. The six theorem audits remain required by the kernel-checking stage.

The [updated preparation receipt](results/full-shape-preparation-v2/results.json) and
[frozen artifacts](results/full-shape-preparation-v2/preparation.tar.gz) retain
the complete controls, source manifest, generated requests and checker logs.
After extracting that archive to a fresh directory, repeat the request/slot checks:

```bash
python3 reproduction/local_models/results/full-shape-preparation-v2/controls.py \
  --repository . --prepared /tmp/extracted-preparation --output /tmp/slot-checks
```

The mathematical semantics use abstract scalar operations. Hardware correspondence
and floating-point behavior retain the existing studies' separate limits.

The controller allows sixteen responses, eight source reads of at most 120 lines,
and three actual Lean proof checks per case. It records syntactic refusals,
proof failures, reasoning-only responses and transport failures separately.
Successful proofs receive a second fresh Lean invocation and axiom audit before
acceptance. This experiment records model proofs, not new registered frontend
source certificates. Its source-bound tasks and generic proof libraries remain
different from the authors' unavailable optimized registry.

All three named open checkpoints use seed `261102028`, temperature zero, 16,384
maximum output tokens and a 4,096-token thinking budget. GLM requests use low
reasoning effort. The controller uses a common 65,536-token context limit and a
256-token margin. Actual server tokenization precedes each inference request.
If context is tight, old library excerpts and bounded prior feedback are removed
in a fixed order; the source, shapes and theorem statements remain complete.

With a fresh pinned ready-server record and a loopback endpoint, run all seventeen:

```bash
LARK_REAL_PROJECT=/path/to/configured/lean-real \
python3 reproduction/local_models/full_shape_run.py \
  --prepared /tmp/extracted-preparation --lean /path/to/lean-4.19.0/bin/lean \
  --model zai-org/GLM-5.3 --server-record /path/to/ready-server.json \
  --url http://127.0.0.1:19085/v1/chat/completions --output /tmp/full-shape-glm
```

Every request, response, usage record, bounded source read, context compaction,
syntax check and actual proof check is retained. Unknown transport outcomes stop
the cohort with explicit partial status. The optional `--case` flag is for a
separately recorded pilot. Test stubs require `--allow-test-stub` and always record
zero real inference calls and zero model-generated proof successes.

The frozen v1 preparation remains available at its original source checkpoint.
V2 incorporates the checker boundary fix. All 85 case requests, source bindings,
SDK blocks and positive/negative Main files match v1 byte-for-byte.
