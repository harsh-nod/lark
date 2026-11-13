# Paper result coverage

**The paper has not been fully reproduced.** Independent experiments are separate
from the authors' reported results. Kernel studies used zero model calls. Free
local GLM and DeepSeek inference is recorded as separate adapted experiments; no paid
model endpoints are used. Hardware evidence is from AMD GPUs.

The [frozen result-by-result audit](paper_results/snapshots/20261112-v21/results/RESULTS.md)
enumerates all 17 tables, seven outer figure groups and 16 additional narrative
anchors in the published preprint. It distinguishes measurements from setup and
method descriptions, binds the published evidence files by hash, and lists the
exact missing inputs. These overlapping items do not define a completion percentage.
It includes production SiLU, wave reduction, complete native weighted and fused
RMSNorm, complete native online attention, complete native RoPE and both fused
QK/RoPE layouts, complete FlashInfer and guarded SGLang RMSNorm, native FP16
single-split-K AWQ GEMM, and the source-bound softmax race/repair studies. It
binds 3,312 published evidence files at commit `3eab929` and can be
replayed after later documentation changes. The
[historical snapshots](paper_results/README.md) are preserved.

[Audited full-shape totals](FULL_SHAPE.md): 34 HIP/CUDA certificates, 170 exact-source
trials and 19,387,200 scalar comparisons per MI350X host. Those counts describe
independent adaptations, not completeness of the original paper.

The later [elaborated Lean-reference numerical study](specification_validation/RESULTS.md)
matched 240 sampled values across twelve production-reference variants and four
input strata. It evaluates actual imported Lean definitions against unchanged
Torch modules on CPU, with explicit identity storage casts in its float64 track.
Its fourteen numerical negative controls and 26 packet mutation controls passed.
This is additional evidence for the tested specification formalizations, with
zero new source certificates, GPU trials or model calls. It is separate from
the immutable v21 ledger and does not recover the authors' registry or results.

The [benchmark-reference CPU study](benchmark_specification_validation/RESULTS.md)
adds 340 sampled output comparisons across all seventeen independent families
and four strata. It also compares every materialized attention score: 589,824
Float64 values matched the unchanged Torch references bit-for-bit. Its fixed
checked Float64 interpretation evaluates the actual polymorphic Lean references;
storage conversions are identities. All 24 numerical negative controls and 41
artifact mutation controls passed. This is independent numerical evidence with
no new certificate, GPU/model call, IEEE theorem or original-paper result claim.
Its fresh-source replay and CI/publication receipts are tracked separately.

[Offline model experiment preparation](local_models/README.md) now identifies
official open weights for GLM-5.3, GLM-5.3-Flash and DeepSeek-V4.1-Flash-1017.
This makes local adaptations possible; it does not recover the original harness
or hosted-model outcomes. The [expanded DeepSeek cohort](local_models/DEEPSEEK_RESULTS.md) completed all 17
reduced families with one model-generated depthwise-convolution certificate,
independently exported/rechecked. Its 51 requests used 821,063 reported tokens.
This does not reproduce the original model experiment.
The [completed three-model comparison](local_models/results/model-comparison-20261109/README.md)
audits the same 17 first-request messages for every checkpoint. GLM produced
one first-attempt SiLU certificate; Flash and DeepSeek produced zero first-attempt
certificates. GLM used 832,937 tokens across 49 requests, Flash 312,772 across
17, and DeepSeek 821,063 across 51. Retry budgets remain separate; these are
independent reduced-fixture results, not the original paper's rates. A separate
[comments-only replay](local_models/COMMENT_REPLAY_RESULTS.md) produced no new
certificates and did not alter the raw model results.

Paper: [LARK, arXiv:2611.02028v1](https://arxiv.org/abs/2611.02028v1).
Studies: [CPU/MI300X](RESULTS.md), [nonlinear/MI350X](nonlinear/RESULTS.md),
[full-length pointwise induction](pointwise/RESULTS.md),
[full-size GEMV/counting-loop induction](reduction/RESULTS.md),
[full-size GEMM/BMM induction](matrix/RESULTS.md),
[full-size Linear with bias](linear/RESULTS.md),
[full-size interleaved RoPE](rotary/RESULTS.md),
[full-size valid Conv2D/depthwise](convolution/RESULTS.md),
[full-length RMSNorm/LayerNorm/Softmax](normalization/RESULTS.md),
[full-size two-launch FFN](feedforward/RESULTS.md),
[full-size SwiGLU with FP32 projections](swiglu/RESULTS.md),
[full-size dense SDPA/GQA](attention/RESULTS.md),
[same-source dot-product proof ablation](dot_ablation/RESULTS.md),
[MI350X shuffle/MFMA conformance](collective_conformance/RESULTS.md).
The [bounded scalar PTX study](ptx/RESULTS.md) separately adds four independent
tiny float32 certificates, direct Lean negative controls and CPU-only assembly
checks; it provides no NVIDIA execution evidence.
The [full-wave HIP shuffle study](shuffle/RESULTS.md) adds five whole-launch
Lean certificates, four direct Lean negative controls and 3,200 exact output-bit
comparisons per MI350X host. It formally integrates full-wave register transport;
the earlier MFMA probes remain hardware-only evidence. A separate
[native MFMA tile study](mfma/RESULTS.md) now adds one whole-launch certificate,
four direct Lean controls and 16,850,944 exact-source output-bit comparisons
per host for one AMD matrix-instruction shape with default modifiers.
The [small upstream-derived vLLM SiLU-and-mul study](production_activation/RESULTS.md)
adds HIP/CUDA certificates at two tokens and hidden width five, four direct Lean
controls and exact-source comparisons against an extracted upstream scalar path
on both hosts. Its intermediate FP16 rounding is retained. It does not recover
the original production adaptations or their model outcomes.

The [optional exact-real semantics check](exact_real/README.md) specializes
existing machine proofs and proves reduction-tree/chunk algebra using pinned
Mathlib. It adds no source certificate, GPU trial or original experimental cell.
The separate native studies connect those components to source-bound complete
launches. Floating-point error theorems remain outside their claims.

The [online-attention value proof](online_attention/README.md) separately proves
the normalized tiled recurrence equals dense softmax over exact reals, with
positive denominators and four checked false-update counterexamples. It is
algorithm algebra only; the upstream infinity sentinel and original-paper
attention artifact remain outside that study.
Separate native checks of the unchanged upstream FP32 online kernel passed
749,568 output comparisons on both MI350X hosts, including the 128×256 workload
and large common score shifts. Every CPU float64 reference was recomputed in an
offline audit. This is not the paper's FP16 adaptation or an additional source
certificate; the original production and Level-2 rows below remain incomplete.
The later [native FP16 online source](online_attention/NATIVE.md) retains the
32-thread tiled algorithm and private running-state arrays. It has checked
source/layout identity, address ownership and conditional footprint lemmas,
a finite value-erased access preflight, and 3,145,728 paired CPU-reference
comparisons across both hosts with zero tolerance failures. The later
[first-block proof](online_attention/BLOCK.md) composes all 32 lane prefixes,
checks actual native scheduling, barrier convergence and resumption, all
block-owned zero outputs, the first full K/V tile, input preservation and
prefix-trace race freedom. Each lane executes 5,405 scalar instructions
before the barrier.
The [compute prefix](online_attention/WEIGHTS.md) adds actual query preparation,
all 32 score dot products and maximum updates, exponential weights and ordered
denominator accumulation for each lane's first query row and first key tile.
It checks a 58,891-instruction per-lane continuation
from PC 21 through PC 56, with values, input preservation and prefix-trace race
freedom. Its frozen packet leaves later computation open.
The [whole-launch checkpoint](online_attention/WHOLE_LAUNCH.md) now joins all four
key tiles, all query rows, every native block and the final halt. It proves
actual complete execution, input preservation, actual-trace race freedom and
extraction of every source-ordered output. A separate canonical-real theorem
connects the unchanged source to dense 128-key, 256-component SDPA for every
group count `1..65535`, with four source-bound exports at 1, 3, 64 and 65535.
Half casts are identities only in that idealization; IEEE equivalence and
floating-point error bounds remain unproved. The complete native source is
unchanged from the paired AMD numerical packet. This independent adaptation
does not recover the original author source, models or H100 results.

The separate [full-wave reduction study](wave_reduction/RESULTS.md) now supplies
those proofs for one independent native wave64 XOR butterfly. One source-bound
exact-real certificate and fresh recheck pass; four direct Lean controls are
rejected. Each AMD host matches the source tree bit for bit on 17,408 outputs.
Ordinary Torch comparisons pass, while cancellation disagreements remain
separate scope evidence. This does not recover an original production source,
floating-point theorem, model outcome or NVIDIA timing.

The [native weighted RMSNorm study](production_rmsnorm/RESULTS.md) adds four
canonical-real source certificates and fresh checks at 1, 3, 64 and 255 rows.
Its theorem proves actual whole-launch execution, actual-trace race freedom
and every reference output for all inputs/outside memory at `1 <= rows < 256`,
width 16,384 and native block1,024/wave64 geometry. Both block barriers and the
logical-16 reduction inside physical wave64 are included. Earlier both-host GPU
measurements total 127,008,768 CPU-reference comparisons with zero tolerance
failures; signed-zero and one-half-ULP differences remain explicit. The profile
does not assert IEEE equivalence, an error bound, the complete upstream API or
an original-paper result. Standalone rebuilds, installed-wheel checks and direct
source/reference/task/model tamper controls pass.

The additional [in-place fused add RMSNorm study](production_fused_rmsnorm/README.md)
pins SGLang's wrapper and its exact FlashInfer dependency. Its complete actual
launch proof covers rows1..255, seeded mutable buffers, all native waves and
both output buffers under the original scheduler and fuel. It derives actual
trace race freedom and retains every rounded residual and normalized output.
The later canonical-real bridge supplies four source-bound exports and fresh
checks, with standalone archive replay. Half casts are identities in that real
interpretation. As in the paper, floating-point behavior is tested numerically;
IEEE/error bounds are outside the formal claims. The original production
artifact remains unavailable. Both AMD hosts complete 24 paired trials. The CPU audit checks
127,008,768 normalized values and 127,008,768 residual bit patterns across both
hosts/methods with zero failures; signed-zero and 475 one-half-ULP normalized
method differences per host remain explicit.

The separate [native llm.c softmax study](production_softmax/README.md) binds
both complete three-pass HIP adaptations to their full translated programs.
Both have complete block proofs under the original fuel. The repaired source
also has whole-grid execution, actual-trace race freedom and source-ordered
output extraction for every supported row count1..42730 at width50257 and
block1024/wave64. Its optional canonical-real theorem proves the dense softmax
formula for all real inputs and any finite seed, with identity half casts and
a positive source denominator. Independent fresh archive replays and scope
guards are saved. Both AMD hosts pass 2,036,413,640 value comparisons with no
tolerance failures. These adaptations do not recover the authors' exact PTX,
NVIDIA timings or historical model results. The original-race proof now reaches
both conflicting accesses in the actual complete original block trace from
initialization and proves a complete supported one-row launch is racy and fails
`Correct` for any reference. The source/replay each audit 1,530 declarations and
reject 11 false claims; all eight CI jobs pass. The development reader still
issues zero registered softmax source certificates.

The [native in-place vLLM RoPE study](production_rope/README.md) now proves the
complete launch, actual-trace race freedom and extraction of both dense-reference
outputs at every supported row count `1..65535`. It retains block512, Q32/K8
heads, width128, both rotary layouts, seeded mutable Q/K buffers, arbitrary
scalar operations and explicit half conversions. Eight registered certificates
and fresh rechecks pass with 157 library and 80 source axiom audits, eight false
Lean claims and eight rehashed integrity/scope controls. Earlier complete finite
traces at one and three rows check 40,960 symbolic values. Both AMD hosts pass
79,626,240 fresh CPU float64/Torch FP32 comparisons, with zero tolerance or bit
differences. This evidence is included in the immutable v20 ledger and does not
replace an original accepted production kernel. IEEE/error guarantees remain outside
the paper's formal scope.

The separate [fused Q/K normalization and RoPE development](production_qknorm_rope/README.md)
retains the native block256, Q32/K8/V8 heads, width128 and logical32 reductions
inside physical wave64. It follows the paper's out-of-place and gathered-cache
departures and proves both complete native launches, actual-trace race freedom,
full output extraction and equality to independent dense exact-real references.
Four interleaved v20 and four split-half v21 source-bound certificates are
published. The independent replays rebuild without Git or an owned compiled
proof cache; split-half reproduces 69 owned modules, 582 axiom audits, four row
specializations and twelve false Lean claims. All twelve latest CI jobs pass.
Both hosts retain 79,626,240 CPU-reference comparisons with zero tolerance
failures or adapted/upstream bit differences; the 3,948 FP16-word disagreements
with rounded Torch FP32 remain explicit. Historical component/prefix packets
retain their earlier scope. Full evidence is included in the immutable v20 ledger.

The manuscript's ten-case production inventory now has independent scoped
coverage for nine accepted families and the rejected original softmax race
case. The [AWQ GEMM profile](production_awq_gemm/REAL.md) now retains the
paper's FP16-weight and single-split-K departures in an explicit AMD wave64
fragment remapping. Four complete sources match the Lean template, with
address/ownership components, universal launch bounds, the actual first block
visit, full 64-lane staging, both native K16 passes, every K32 iteration,
guarded converted output stores and complete initialized grid execution and
termination with the original fuel. Its full source certificate additionally
proves actual whole-trace race freedom, complete output extraction and
independent dense exact-real equality. Four exports and rechecks pass;
standalone replay reproduces 734 axiom audits over 83 owned modules and 14
logical rejections. Thirty-eight rehashed scope claims fail before extraction.
Four finite launches match 18,048 output expressions and
359,424 trace events. Paired MI350 runs check 820,224 outputs over 120 launches
with no tolerance failures or host bit differences. The full AWQ profile
adds the ninth independent family with four source certificates.
Original sources, model runs and hardware
measurements remain separate missing inputs. The immutable v21 ledger includes
the complete FlashInfer, SGLang and AWQ profiles; earlier snapshots retain
their historical scopes.

The [complete FlashInfer RMSNorm profile](production_flashinfer_rmsnorm/README.md)
proves actual guarded native whole-launch execution, actual-trace race freedom
and dense exact-real reference equality at width16384 and rows1..131072. Four
complete-source exports and rechecks, a frozen replay without Git or owned
compiled objects, source/reference/tamper controls and installed-wheel checks
pass. Its 68 owned modules, 490 library audits and four eight-audit Main
instances contribute 522 audit occurrences. Paired AMD runs retain 127008768
CPU-float64 comparisons with zero tolerance failures. Measured signed-zero and
one-half-ULP differences remain explicit; no original-paper or IEEE result is
claimed.

The [complete guarded SGLang RMSNorm profile](production_sglang_rmsnorm/CANONICAL_REAL.md)
likewise proves the actual whole native launch, actual whole-trace race freedom
and every dense weighted RMSNorm reference output for all rows1..131072 at
width16384. It retains both reductions, both barrier resumptions, all three
private half[16] caches, paired arithmetic, block1024/wave64 and logical32.
Four complete-source exports/rechecks and an independent frozen-source replay
pass 782 axiom-audit occurrences over 88 owned modules; eighteen false Lean
claims are rejected again in that replay. The source checker records forty
proper refusals, and 32 fully rehashed scope controls reject overclaims before
extraction. Installed-wheel checks and anonymous public-source download/binding
checks pass. The earlier numerical packet retains 144 AMD launches and
190513152 CPU-float64 comparisons with zero tolerance failures. Its lane-zero
partial-store guard is explicit. The original unguarded adaptation's reached
conflict, earlier proof stages and original-paper scope remain separate.

| Paper result | Available evidence | Remaining work or dependency |
| --- | --- | --- |
| Level-1 pass rates and per-task results (§5.1, A.4.1) | Independent reduced CUDA/HIP certificates; four tiny scalar PTX certificates; full-size independent CUDA/HIP proofs and exact-source MI350X checks for all twelve Level-1 families | Authors' pinned kernels/registry and harness, original model endpoints/runs, optimized PTX and broader instruction support |
| Five Level-2 PTX proofs (Table 3) | Five independent reduced HIP proofs; full-size HIP/CUDA RoPE, two-launch FFN, four-launch SwiGLU and three-launch dense SDPA/GQA certificates; independent native tiled online attention now has complete execution/race proofs and four canonical-real exports | Original PTX kernels/GQA project, original optimized attention adaptations, NVIDIA launches and collectives |
| All 42 original mutants and rejection channels (§5.2, Tables 4/15) | Independent 28-mutant nonlinear CUDA/HIP study, prior scalar/proxy mutants, six full-length arithmetic mutants and four tiny PTX controls checked directly in Lean | Original mutants/harness, original PTX coverage, model-based diagnosis and second opinions. Independent sets are not the original 42 |
| Nine accepted production kernels (§5.3, Table 5) | Nine independent upstream-derived families: SiLU-and-mul, weighted RMSNorm, fused add RMSNorm, online attention, in-place RoPE, fused QK/RoPE, FlashInfer RMSNorm, guarded SGLang RMSNorm and native FP16 AWQ GEMM. Their respective fixed profiles publish 8, 4, 4, 4, 8, 8, 4, 4, 4 source-bound exports, with standalone replays and paired-host numerical checks. AWQ retains complete native MFMA snapshots, all K tiles and guarded converted stores; its full proof covers actual execution/race freedom/extraction and dense real equality | The paper's exact FP16 single-split-K PTX adaptation; all original adapted files, revisions, signatures/departures, proof projects and model outcomes. These independent families do not reproduce the original nine |
| llm.c data race | Full-source native HIP binding, actual reached conflicting accesses, complete original one-row launch counterexample, repaired whole-grid execution/race freedom and canonical-real softmax, complete finite traces and paired both-host numerical checks | Exact paper registry revision/author-adapted PTX and original NVIDIA experiments |
| Failure-analysis ablations and costs (§5.4, A.4.9) | Deterministic diagnostics, failed proof artifacts, and a separate comments-only replay of two refused DeepSeek candidates (both still unproved) | Original models, prompts, budgets and failures; offline/free constraint excludes paid endpoint calls |
| Segmentation/flat ablation (§5.4, A.4.8) | Pointwise and counted-loop GEMV/GEMM/BMM induction concluding existing machine `Correct`; same-source pointwise and GEMV flat/induction timing comparisons (GEMV flat verified through K=16, timed out at K=32/64/128; induction verified/rechecked all eight sizes) | Original kernels, agent prompts and LLM runs; scalable profiles use one-thread blocks |
| Verification scaling (A.4.4) | Independent ReLU proofs through length 2^31-1, GEMV/GEMM reduction through K=1,048,576 BMM output footprints through 2^30, all three normalization families through N=2^31-1, connected attention through 4,096-token rows / 1,048,576-wide projections, and native online attention for 1..65535 groups at N128/D256 | Original kernels, other optimized attention shapes, original token/time measurements |
| Model size versus pass rates/tokens (A.4.6) | Completed 17-fixture cohorts for GLM, Flash and DeepSeek with identical decoded first requests; first certificates 1 / 0 / 0, separate retry results 1 / 0 / 1, audited table and SVG | Original model versions, harness, token accounting and runs; tokenizers/precision/TP differ, so no isolated model-size conclusion |
| Stage token costs (A.4.3) | Completed matched cohorts: GLM 832,937 tokens / 36 Lean checks, Flash 312,772 / 7, DeepSeek 821,063 / 37; earlier pilots and reasoning-only runs archived separately | Original stage traces/endpoints and stage boundaries; local inference does not reproduce billed costs |
| Refusal census and hard Level-1 tasks (A.4.2/A.4.5) | Strict refusals; full-size independent BatchMatmul/DepthwiseConv certificates and device checks | Original failed runs/statements; smaller proofs do not contradict the paper's model outcomes |
| Race-freedom fallback (A.4.7) | llm.c conflict witness, generic pointwise ownership and complete actual-trace classification for native RMSNorm and online attention | Original fallback conversations, second opinions and token costs |
| Latencies/speedups (A.4.10, Table 14/Figure 7) | Independent 17-workload FP16 numerical checks and eager/compiled timings on MI300X/MI350X | Authors' optimized kernels/reference contracts, fastest vendor baselines, H100 for original PTX/CUDA cells |
| Per-operation conformance (A.5) | Eight scalar operation samples on AMD; exhaustive finite-half decode/roundtrip, sampled FP32-to-half conversions, full-partition shuffle layouts and one native MFMA shape with exhaustive basis-pair probes on two MI350X hosts; five shuffle certificates, one native MFMA tile certificate and complete aligned logical-16 reduction execution inside native RMSNorm | Full instruction table, other combined/tiled collective programs, arbitrary sparse masks and other vector/alignment/collective forms and modifiers, NVIDIA hardware for NVIDIA operations. Samples are not complete semantics |
| Retargeting effort/source counts (A.6) | Independent CUDA/HIP and bounded scalar PTX readers sharing a machine | Authors' source tree and development history; historical person-days cannot be regenerated by an independent implementation |
| Supplementary GQA project (A.12) | Full-size three-launch GQA certificate, source-bound FP32 intermediates and exact-source checks on both MI350X hosts | Authors' actual supplementary project not found in the manuscript source archive or searched release endpoints |

The [artifact audit](pointwise/results/artifact-audit.json) and
[repeated public checks](results/artifact-reaudit-20261110.json) record specific public
GitHub queries and the empty `AICrossSim/KernelCraft` metadata. The [arXiv source
inventory](results/paper-source-manifest.json) has manuscript files/figures and no
implementation. These bounded searches do not prove that artifacts cannot exist
elsewhere or be released later.
The later [complete-page query record](paper_results/original-artifact-full-query-20261112/results.json)
retrieves all 256 returned repository names/metadata for one `LARK Lean GPU`
query, below GitHub's 1000-result cap. The known GPU/Lean candidate describes
an independent project and cites LARK as related work. Other terms, private or
unindexed code, repository contents and unsearched branches remain outside this
query; no original implementation was identified from its inspected metadata.
The [expanded author-repository check](results/artifact-expanded-20261110.json)
also records the public `gpu_optim_bench` repository: its inspected revision
identifies itself as FlashInfer-Bench and has no LARK/Lean/KernelCraft-named
path or Lean/PTX/HIP file in its complete tree. This bounded tree/README check
does not exclude relevant material elsewhere.

All 17 workload shapes now have independent full-size contracts and exact-source
HIP checks. The separate native online-attention study also has a complete
four-tile launch and dense-real reference proof at N128/D256. Remaining software
work includes other optimized/tiled/vectorized production kernels, broader PTX
and collective semantics, original adapted production sources, and corresponding
hardware validation. It cannot recover missing original model outcomes, source
revisions, historical development effort or H100 measurements. AMD adaptations
and independent experiments remain labeled as such.
