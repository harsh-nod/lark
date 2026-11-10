# Small vLLM scalar SiLU-and-mul adaptation

**This is not a reproduction of the paper's original production kernels or pass
rates.** It certifies one independent adaptation of a pinned public vLLM scalar
path, at two tokens and hidden width five. The paper's actual adapted source,
revision, signature and production configuration remain unavailable.

| Check | Result |
| --- | ---: |
| HIP/CUDA whole-launch Lean certificates | 2 / 2 |
| Fresh certificate rechecks | 2 / 2 |
| Direct Lean negative controls | 4 rejected, 0 accepted, 0 timeouts |
| Independent AST versus CPU reference comparisons | 10,240 |
| CPU outputs changed by omitting intermediate half rounding | 2,614 / 10,240 |
| Model calls | 0 |

The certificates prove completion, race freedom and every output for all inputs
and outside memory in the declared abstract-operation machine. The independent
reference retains the half conversion inside SiLU before the gating multiply.
Both positive proofs use only `propext` and `Quot.sound`. The four controls drop
that conversion, change the token stride, select the wrong gating half, or omit
the last output. Each reaches Lean directly and fails the output-equivalence
proof; this is rejection of the supplied proof, not a complete decision procedure.

| Host | Input trials | Kernel launches | Adapted / upstream output values | Bit differences | CPU comparisons | Max absolute error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| mi350, physical GPU 2 | 1,024 | 2,048 | 10,240 / 10,240 | 0 | 20,480 | 0 |
| mi350-2, physical GPU 0 | 1,024 | 2,048 | 10,240 / 10,240 | 0 | 20,480 | 0 |

Each trial runs the exact certified HIP bytes and a scalar specialization
extracted from the archived upstream helper bodies and loop. The latter uses
the actual `torch::headeronly::Half` carrier, with eight pinned header files
from CPU PyTorch 2.11.0+cu130 (commit recorded in the provenance). The GPU hosts
need those headers at compile time, with no PyTorch runtime. Each method is
checked against CPU PyTorch at `atol=rtol=0.002`; the observed error was zero.
All input bytes and 128-byte guards on both sides of all three allocations
remained unchanged. Fresh activity/memory guards selected idle GPUs, and other
jobs were left untouched. ROCm compilers differed across the two hosts.

The source rewrite is not itself verified, and the original complete templated
translation unit is not certified. The trusted operation semantics and the
finite numerical comparisons do not establish general IEEE behavior. These
small shapes do not establish scalable or optimized production coverage. CUDA
has CPU proof evidence only; no NVIDIA execution occurred. These counts are
separate from the seventeen-family full-shape ledger.

The initial comparison builds on both hosts failed before execution because a
native HIP half specialization made the upstream mixed-type multiplication
ambiguous. The corrected specialization uses PyTorch's half carrier. The two
failed build archives and their original input packet are retained; they are
not GPU trials, proof failures or additional mutation outcomes. The certified
kernel, independent reference and task did not change. CPU and corrected GPU
source snapshots are separately recorded.

The [evidence auditor](summarize.py) verifies the frozen manifests, regenerates
every GPU input file from the corrected source snapshot, compares both raw
device output streams and checks all numerical values. A control changes an
output bit and recomputes its report/archive hashes while retaining a claimed
passed status; the auditor rejects the raw-stream disagreement. This audit
performs no fresh Lean, GPU or model execution.

```bash
python3 reproduction/production_activation/summarize.py \
  --results reproduction/production_activation/results
```

[Machine-readable summary](results/summary.json), [validation](results/validation.json),
[CPU proofs and controls](results/cpu-20261110/), [raw evidence manifest](results/manifest.json),
[upstream revision and rewrites](provenance.json). The archived GPU generator's
exact CPU PyTorch version is required for byte-for-byte dataset regeneration.
