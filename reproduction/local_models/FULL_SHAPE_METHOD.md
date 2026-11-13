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

`audit_full_shape.py` replays a completed recording through the same fixed
protocol with recorded model/tokenizer responses. It regenerates every prompt,
bounded source read and submitted Main from the frozen preparation. Captured
Python remains data. A recording validation refusal stops acceptance even if a
record labels it as a transport failure. Model calls, tokenizer requests and
new registered source certificates from the audit are zero.

```bash
LARK_REAL_PROJECT=/path/to/configured/lean-real \
python3 reproduction/local_models/audit_full_shape.py \
  --recording /tmp/full-shape-glm --prepared /tmp/extracted-preparation \
  --output /tmp/full-shape-audit --lean /path/to/lean-4.19.0/bin/lean \
  --require-full-cohort
```

The full-cohort requirement rejects a pilot or partial recording. Omit it only
when explicitly auditing that narrower scope. `--lean` runs a fresh proof-term
syntax check and two real kernel/axiom checks for every recorded success. Without
it the audit checks protocol and recorded-log consistency, reports zero freshly
verified proofs, and makes no fresh theorem-validation claim. Failed candidates
retain their recorded outcomes; this auditor does not rerun their Lean checks.
Reported model tokens remain distinct from the audit's zero model calls.

`compare_full_shape.py` aggregates complete, archived seventeen-task cohort
packets. It checks both archive inventories, receipt/response token usage,
per-case outcomes and the recorded fresh accepted-proof bindings. It applies
the paper's cost definition separately to the twelve Level-1 and five Level-2
families: mean input/output tokens over tasks that eventually verify. Each
successful task's cost includes its source reads and unsuccessful proposals.
Failed-task spending remains in the separately reported all-task totals.
With zero verified tasks, the success-only mean is undefined, rather than zero.

The separate [manuscript arithmetic check](../paper_results/level2-cost-arithmetic-v1/RESULTS.md)
finds a discrepancy in the published Level-2 GLM totals: displayed input/output
means of 373.90M/9.29M match all five tasks, whereas the caption's successful-task
rule gives 71.90M/2.70M. The independent comparison uses the caption's definition
and keeps failed-task costs in its all-task totals. This observation concerns
the displayed cells, without access to the authors' unrounded usage or logs.

```bash
python3 reproduction/local_models/compare_full_shape.py \
  --packet reproduction/local_models/results/full-shape-cohort-deepseek-v1 \
  --allow-partial-roster --output /tmp/full-shape-comparison
```

The complete independent roster is three pinned open models on two source
languages. A smaller roster requires the explicit flag above; duplicate
model/language inputs, partial cohorts and stubs are refused. JSON preserves
the missing inputs and separates first-response from first-actual-Lean-check
success. This report makes no model calls and reruns no protocol, Lean or GPU
experiment. Its recorded proof counts refer to the separate bound replay,
not fresh checks by this aggregation. These metrics describe the independent
fixed-scaffold tasks; they do not recover the paper's original 144 cells,
closed models or PTX results. The Level-2 attention fixture is dense SDPA.

The controller also recognizes the separately pinned
[CUDA preparation](results/full-shape-cuda-preparation-v1/results.json). Its
seventeen existing CUDA fixtures retain their original buffer shapes, dtypes,
fuels and native warp width of 32. Seventeen SDK positive checks and seventeen
all-masked negative checks passed on CPU under the same Lean limits. This adds
no CUDA execution, NVIDIA measurements, model calls or source certificates.

```bash
LARK_REAL_PROJECT=/path/to/configured/lean-real \
python3 reproduction/local_models/cuda_shape.py \
  --lean /path/to/lean-4.19.0/bin/lean --output /tmp/full-shape-cuda-preparation
```

Use that frozen preparation with the same `full_shape_run.py` command and model
budgets. The known manifest fixes the source language; new run reports label it
explicitly and capture the CUDA preparation driver as an additional dependency.
The auditor checks that dependency and refuses a CUDA label attached to an old
HIP preparation or to a controller that only supported HIP. Historical HIP
records remain supported. The active HIP cohorts continue with their original
frozen controller and inputs. No CUDA model success is claimed by preparation.

The [paired-reference check](results/hip-cuda-reference-identity-v1/binding.json)
proves equality of the actual generated HIP/CUDA specification functions for all
seventeen families. Each new Main retains both SDK blocks inside separate
namespaces and checks their twelve original obligations plus the function-equality
theorem. All 221 axiom audits passed. The paired Torch reference files are also
byte-identical. This establishes shared formal specifications at the existing
shapes; the earlier CPU numerical sample counts remain unchanged.

```bash
LARK_REAL_PROJECT=/path/to/configured/lean-real \
python3 reproduction/local_models/reference_identity.py \
  --hip-prepared /tmp/extracted-hip-preparation \
  --cuda-prepared /tmp/extracted-cuda-preparation \
  --lean /path/to/lean-4.19.0/bin/lean --output /tmp/reference-identities
```

The wrong-operator control pairs the ReLU and GELU specifications. Its reflexivity
attempt reaches the fixed recursion limit only in the final identity proof,
after both original source-proof audits pass. It is refused without a certificate;
this resource refusal is not a semantic inequality proof. The development draft
misclassified that diagnostic; the final run corrects the classification while
retaining identical Main bytes, shapes, fuels and limits. The study adds no
model calls, numerical samples, GPU executions or registered source certificates.
A separate CPU CI job repeats all seventeen identities and the refusal while
retaining the eighteen existing jobs.
