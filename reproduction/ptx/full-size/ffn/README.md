# Full-size compiled FFN development proof

These are exact inputs from the independently published full-size compiler
study. `input-bindings.json` binds every file to its original archive member.
The first launch computes a 64×256 by 256×1024 matrix product, ReLU and an FP16
store. The second reads that complete 64×1024 FP16 intermediate and multiplies
by a 1024×256 matrix. The supplied reference preserves both FP16 round trips.

The development frontend checks both fixed contracts and losslessly reads all
173 and 171 instructions, including their original loop limits. It keeps grids
65,536 and 16,384, block size 1, warp size 32, and CUDA fuel 1,030 and 4,102.

The independent Lean tensor interpreter now proves the complete reference
denotation and extraction of all 16,384 output elements, including both FP16
round trips. Its generic shape and fold lemmas avoid reducing the entire
concrete matrix product inside Lean's kernel. The original proof limits remain
unchanged. The latest source build passes all 22 axiom audits; failed development
attempts and the successful checks remain in `development/`.

Rebuild both owned Lean modules and the exact reference-input binding from
source using the pinned Lean 4.19.0 binary:

```sh
python3 reproduction/ptx/check_ffn_reference.py \
  --lean /path/to/lean-4.19.0-linux/bin/lean --output /new/output/directory
```

The complete compiled up stage now has a source-bound Lean development proof.
It covers all 173 parsed instructions, the real 256-term loop, ReLU, FP16 store
and return, all 65,536 lanes and reference outputs, access-trace race freedom,
and memory preservation outside the output region. Its specification uses the
independent tensor interpreter above. The reusable checker also binds the
complete original reference AST. Its fresh source build checks nine owned
library modules plus the generated input binding, with 220 axiom audits.

```sh
python3 reproduction/ptx/check_ffn_up.py \
  --lean /path/to/lean-4.19.0-linux/bin/lean --output /new/up-stage-directory
```

The down stage now also has a complete source-bound proof: its original
47-instruction prologue, all 64 sixteen-term iterations, FP16 store, return,
16,384 outputs, race freedom and memory frame are checked. Its tensor
specification independently performs the 64×1024 by 1024×256 product.

The composed proof binds both kernels to five shared logical allocations.
The second launch reads the actual FP16 intermediate written by the first.
It proves both complete executions, every final reference output, preservation
outside the intermediate and output regions, and race freedom of the combined
access trace. Accesses retain the model's reverse chronological order. The
sequential host launch boundary gives the two launches separate grid-epoch
namespaces. Symbolic proof parameters are specialized to exactly 65,536 and
16,384 lanes; the workload and proof limits remain unchanged.

```sh
python3 reproduction/ptx/check_ffn_pipeline.py \
  --lean /path/to/lean-4.19.0-linux/bin/lean --output /new/pipeline-directory
```

The complete source checker rebuilds fourteen owned libraries and the generated
two-program/reference input binding, with 256 axiom audits. This is two proved
stages and one sequential pipeline under the declared scalar-operation,
logical-pointer and host-launch interpretation. A separate development
certificate now exports both PTX inputs, both unchanged contracts, the complete
reference, generated Main, all owned sources and the actual kernel-check logs.
Replay checks the complete recording inventory and regenerates Main with the
current installed trusted checker. It rebuilds all fourteen Lean libraries
from current matched source; captured Python, Lean and compiled objects remain
data. No captured reference module is executed.

```sh
python3 -m lark_kernels.ptx_ffn_certificate verify \
  --up-source reproduction/ptx/full-size/ffn/up/kernel.ptx \
  --down-source reproduction/ptx/full-size/ffn/down/kernel.ptx \
  --reference reproduction/ptx/full-size/ffn/reference.py \
  --up-contract reproduction/ptx/full-size/ffn/up/task.json \
  --down-contract reproduction/ptx/full-size/ffn/down/task.json \
  --lean /path/to/lean --output /new/export
python3 -m lark_kernels.ptx_ffn_certificate replay \
  --recording /new/export --lean /path/to/lean --output /new/replay
```

Four direct Lean controls change the up-stage ReLU, shorten the down-stage
reduction, remove the intermediate half cast, or disconnect the second launch
from the actual first-launch memory. The first two use the lossless frontend;
the latter two deliberately bypass Python preflight to test the Lean proof's
dependencies. Each fails at its intended proof without a resource failure.
Another 31 complete, coherently rehashed false recordings are rejected before
fresh Lean work, including false scope/counts, larger caps, altered host order,
rebound intermediate, missing audits, and changed captured code or reference.
These controls are not the paper's original mutation set or a general
classifier of incorrect kernels.

`certificate-development-v1/` retains the export/replay check logs, direct
controls, recording-control results and complete original inventory hashes.
An isolated wheel installation reproduced the proof using only installed
trusted Python and Lean sources. Complete original payload directories remain
retained; the published development receipts do not claim to contain those
entire payloads. Their full archive publication is still pending.

```sh
python3 reproduction/ptx/check_ffn_source_controls.py \
  --recording /new/export --lean /path/to/lean --output /new/source-controls
python3 reproduction/ptx/check_ffn_recording_controls.py \
  --recording /new/export --lean /path/to/lean --output /new/recording-controls
```

The unchanged limits are 10,000 recursion depth, two million heartbeats,
180 seconds per Lean process, 600 seconds per complete fresh source build,
and the original 8 MiB stack. Full release validation, complete evidence
publication and integration into the complete paper ledger remain unfinished.
This adds zero registered certificates and zero original paper results.
There is no original optimized-program, IEEE guarantee or NVIDIA-execution
claim. Failed and accepted development attempts remain alongside their evidence.

Earlier hosted FFN source checks used the runner's actual 16 MiB stack default;
their raw reports retain that value. The three local certificate checks used
8 MiB. New certificate CI steps explicitly set 8 MiB before execution; their
execution is a separate pending validation gate.
