# Finite FP16 PTX pointwise proof

The separate `ptx-fp16-pointwise-finite-v1` development checker proves the exact
compiled ReLU program from the [full-size CPU assembly study](results/full-size-compilation-v1/RESULTS.md).
It covers 16,384 FP16 elements, 16,384 blocks with one thread each, and all 15
instructions in the actual PTX 8.8/sm_80 program. The original independent CUDA
reference contract, shape, dtype, geometry, reference and source bytes are
retained. This scalar launch is not an optimized kernel from the paper.

The [recorded proof packet](results/full-size-relu-proof-v1/RESULTS.md) contains
one exact-source development proof and three fresh rechecks, including replay
from an installed wheel outside the checkout. Four accepted-grammar mutations
fail directly in Lean without timeout. Existing HIP/CUDA model cohort results
and legacy SDK profile counts are unchanged; this module has its own CLI.

## Repeat the recorded source-only check

Install this revision with `python3 -m pip install .`, or run from its checkout.
The checker requires the hash-pinned Linux x86-64 Lean 4.19.0 release binary
(SHA-256 `92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023`).
It supports a matching executable path or an elan shim that resolves to that
toolchain. Choose fresh output directories outside any Git checkout.

```bash
mkdir /tmp/lark-ptx-recorded-export
tar -xzf reproduction/ptx/results/full-size-relu-proof-v1/export.tar.gz \
  -C /tmp/lark-ptx-recorded-export

python3 -m lark_kernels.ptx_pointwise_certificate replay \
  --recording /tmp/lark-ptx-recorded-export \
  --lean /path/to/lean-4.19.0/bin/lean \
  --output /tmp/lark-ptx-fresh-replay
```

Replay checks the complete recording inventory, current trusted source
identities, input and Main hashes, theorem/axiom/resource metadata, and exact
regeneration of the parsed translation and Main. It compiles all three owned
Lean modules from current source into a fresh import root and checks Main
again. Captured Python, Lean and oleans are data; no old owned olean cache is
used. The checked toolchain supplies the Lean standard library.

To create a new export from those exact inputs:

```bash
python3 -m lark_kernels.ptx_pointwise_certificate verify \
  --source /tmp/lark-ptx-recorded-export/kernel.ptx \
  --reference /tmp/lark-ptx-recorded-export/reference.py \
  --contract /tmp/lark-ptx-recorded-export/contract.json \
  --lean /path/to/lean-4.19.0/bin/lean \
  --output /tmp/lark-ptx-new-export

python3 reproduction/ptx/check_pointwise_controls.py \
  --recording /tmp/lark-ptx-recorded-export \
  --lean /path/to/lean-4.19.0/bin/lean \
  --output /tmp/lark-ptx-source-controls
```

## Proof and trust boundary

The closed lossless reader handles exactly two positional `.param .u64`
arguments, typed `.b16/.b32/.b64/.f32` declarations, parameter loads, generic to
global pointer conversion, block ID, signed wide multiplication and pointer
addition, half loads/stores, half/float conversions, finite hexadecimal float
literals, selected scalar arithmetic and terminal `ret`. It preserves comment
and whitespace readback and requires end of input. Unsupported syntax is
refused. Parsing support alone does not certify another program.

The immutable Main proves equality between the actual parsed instruction list
and the library's proved program, and between the closed reference AST and its
proved body. It then proves launch completion, race freedom for actual memory
events, segment equivalence and the full output specification. The interpreter
tracks initialized registers, shared integer/pointer register slots, pointer
provenance, signed ranges, two-byte alignment, bounds and termination. The
whole-grid argument covers every declared block and output.

The unchanged CUDA contract's fuel `[4,1,1,1]` is recorded as data for its
separate CUDA model. PTX execution is structurally finite and executes every
one of the 15 parsed instructions. This introduces a separate semantics rather
than increasing CUDA fuel. New PTX library/Main limits are `maxRecDepth=10000`,
`maxHeartbeats=2000000`, 180 seconds per Lean process and 600 seconds for the
source import build. No limit was increased for these recorded checks; legacy
libraries retain their existing settings.

The reader, reference formalization, abstract scalar-operation/ABI
correspondence and aligned, disjoint, non-wrapping allocation assumptions
remain trusted. The proof does not establish IEEE floating-point or error-bound
equivalence, arbitrary scheduling conformance on NVIDIA, generated SASS
correctness, or timing. The other full-size PTX families, original optimized
programs and original model experiment harness/results remain unfinished.

Six Main and 22 library axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`. Four source-binding controls change arithmetic, byte stride,
store address and half conversion. They are reader-accepted and Lean-refused at
the exact program equality proof; they do not classify arbitrary false kernels
or reproduce the paper's 42 mutants. Repeated proof checks count as one kernel.
