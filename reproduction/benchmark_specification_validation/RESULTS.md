# Benchmark-reference numerical results

**The original paper is not fully reproduced.** This independent CPU study
evaluates the repository's registered mathematical references at their existing
HIP-case shapes. It adds no kernel certificate, GPU trial, model call, IEEE
equivalence theorem or floating-point error bound.

All **340 sampled final-output comparisons passed**: seventeen families, four
input strata and five output positions. Absolute and relative tolerances are
each `1e-10`. The maximum absolute difference was `2.5579538487363607e-13`.

| Mathematical reference | Comparisons | Maximum absolute difference |
| --- | ---: | ---: |
| ReLU | 20 | 0 |
| SiLU | 20 | 1.38778e-17 |
| GELU | 20 | 1.11022e-16 |
| RMSNorm | 20 | 4.44089e-16 |
| LayerNorm | 20 | 8.45990e-14 |
| Softmax | 20 | 9.05309e-18 |
| GEMV | 20 | 0 |
| GEMM | 20 | 0 |
| BMM | 20 | 0 |
| Linear with bias | 20 | 0 |
| Conv2D | 20 | 0 |
| Depthwise convolution | 20 | 0 |
| RoPE | 20 | 0 |
| FFN | 20 | 0 |
| SwiGLU | 20 | 2.55795e-13 |
| Dense attention | 20 | 1.55431e-15 |
| GQA | 20 | 1.55431e-15 |

All **589,824 materialized score values matched Torch bit-for-bit**: 65,536
dense-attention scores and 524,288 GQA scores across four strata. This enumerates
the score tensors for the recorded inputs. Final outputs remain sampled; no
claim covers every possible input.

The strata are dyadic values, seeded normal values, sparse basis values with
signed zero, and alternating values with small perturbations. Inputs are first
quantized to their declared storage dtype. Storage conversions are identities
in both the Lean Float64 interpretation and the unchanged Torch reference.
Actual-dtype Torch outputs are retained separately and are not asserted equal
to the idealized reference.

The SDK validates each source, task and reference, then renders its actual
polymorphic `spec`. The evaluator checks the complete declaration closure before
unfolding, records the elaborated `List Real` reference, and evaluates the same
generic declaration with fixed checked Float64 operations. Attention reuses
scores only after exact source-call matching. The original/compiled scalar
expressions and every cache/oracle bit pattern are retained. Torch telemetry
records the actual softmax input and was checked to preserve final outputs.

Sources were frozen at `f7c0ecc0c416786337e72a90bb43a4bba348cc57`. The source
manifest SHA256 is
`e635d0ee3517069b62d49f9d59c9fd49f022953df8c64d758e745b3795697da8`.
Lean 4.19.0 and CPU PyTorch `2.11.0+cu130` were used with GPU visibility disabled.
The 68 numerical case processes took **750.17 seconds**, excluding setup,
import builds, controls and Torch oracle generation. Each numerical process
kept the 180-second limit. Every new Lean module/Main kept recursion depth
10,000 and two million heartbeats. Shapes, stack limits and proof fuel did not change.

All **24 numerical negative controls** passed. The
[packet mutation receipt](results/benchmark-float64-packet-controls-v1/results.json)
also rejected **41 altered scope/data cases** after bypassing outer archive
hashes and synchronizing changed case/log hashes where needed. These include
false paper/IEEE/GPU claims, missing workloads, resource changes, wrong values
and types, altered caches/oracles, changed telemetry, invalid inputs, accepted
refusal controls and changed source pins.

The [frozen packet](results/benchmark-float64-v1/manifest.json) binds **145 source
files and 450 evidence files** in two archives. Including the standalone verifier
and result records, it is approximately 68.9 MB. Its audit checks source binding,
protocol scope and numerical consistency. Fresh source replay is running;
its receipt, anonymous publication check and exact-source CI/main gate are pending.

The authors' original registry, formalizations, validation dataset, model pass
rates, token history and NVIDIA measurements remain unreproduced. This protocol
and its independent corpus do not fill those gaps. The separate
[production study](../specification_validation/RESULTS.md) retains its own 240
sampled comparisons and publication/replay receipts.
