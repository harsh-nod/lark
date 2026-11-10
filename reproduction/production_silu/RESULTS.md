# Multiwave scalar SiLU-and-mul results

The native scalar launch and strided loop now have **eight source-bound Lean
certificates and eight independent rechecks**: HIP/CUDA at three device-test
shapes, plus two symbolic-only HIP extremes. Five direct Lean controls were
rejected with zero acceptance or timeout. The local full suite passed all
131 tests in 924.598 seconds; the seven new profile tests passed in 100.239
seconds. The Lean library build passed.

| Host | Physical GPU | Trials | Kernel launches | Outputs per method | CPU comparisons, both methods | Adapted/upstream bit differences | Maximum absolute error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| mi350 | 2 | 30 | 60 | 2,966,860 | 5,933,720 | 0 | 0 |
| mi350-2 | 0 | 30 | 60 | 2,966,860 | 5,933,720 | 0 | 0 |

Each host ran ten trials at each of the three [declared shapes](README.md).
The two methods are the exact certified HIP adaptation and an extracted scalar
specialization of the pinned upstream helper and loop. Both matched CPU PyTorch
with zero observed numerical error under the declared `atol=rtol=0.002` check.
Inputs and both 128-byte guards around each allocation remained unchanged.
Native wave64 and 1,024-thread block capacity were checked at runtime. All
allocations were freed and both one-off processes exited.

CPU preparation separately compared 2,966,860 reference-AST outputs bit for bit
with the original PyTorch reference, with zero differences. Dropping the
upstream helper's intermediate half rounding changed 529,104 outputs. This is
a CPU rounding comparison, not a GPU mutation experiment.

The four source controls change the input-half offset, strided-loop increment,
last-column bound, or intermediate rounding. They bypass Python profile
preflight and fail Lean's fixed-program equality gate. The fifth keeps the
source intact and changes the independent formal reference node; it fails
reference-expression equality. Its `reference-node.json` records that change;
the Python reference file remains canonical. These are rejection of supplied
statements/proofs, not the paper's original mutant set or diagnosis channels.
Lean error recovery prints `sorryAx` after a failed declaration in these
**rejected** negative logs; no accepted certificate contains it.

All positive theorems use only `propext`, `Classical.choice` and `Quot.sound`
where printed. They cover every scalar input and arbitrary initial outside
memory for the fixed native launch, rather than just the numerical samples.
The two billion-cell certificates use induction and constant-size statements;
their arrays were not allocated or executed. They are not included in the GPU
counts above.

[summary.json](results/summary.json) records the independent evidence audit.
It reconstructs all eight positive and five negative statements from the frozen
source, regenerates every GPU input file and checks both raw output streams.
The [fully rehashed divergence control](results/rehashed-stream-control.json)
changed one output bit and recomputed its reported output/archive hashes while
retaining success flags. The auditor rejected the actual stream mismatch.
Audit replay makes zero fresh Lean/GPU/model calls.

[validation.json](results/validation.json) and [manifest.json](results/manifest.json)
bind raw CPU exports/logs, the 106-file frozen source, input packet, host
archives and local validation records. The separate `lark check` of an installed
wheel runs outside the repository; frozen PTX, shuffle and MFMA evidence audits
also replay successfully. The first wheel-build attempt used the host's old
setuptools and failed before building; the isolated build uses the declared
build requirements. Both logs are retained.

This is **one independent function family**, derived from a public November 10
vLLM revision. It does not establish any original production pass rate, original
kernel timing or optimization gain. Packed vector fast paths, in-place aliases,
general optimized kernels, the authors' nine accepted production sources/proofs,
IEEE/error-bound theorems and NVIDIA execution remain missing. The source
rewrite from the templated upstream file is documented and numerically tested,
but is not itself proved equivalent for all inputs. Model calls and billed
model costs are zero; the original paper is not fully reproduced.
