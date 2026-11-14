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
logical-pointer and host-launch interpretation. Certificate export/replay,
adversarial controls and full release validation remain unfinished; it adds
zero registered certificates and zero original paper results. There is no
original optimized-program, IEEE guarantee or NVIDIA-execution claim. Both
failed and accepted development attempts are retained alongside their evidence.
