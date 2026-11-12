This study independently selects SGLang's
`rmsnorm_cta_double<16384,false,fp16_t>` at
[`fc32cbff6983c7573f4b60eab8b44815668130a0`](https://github.com/sgl-project/sglang/blob/fc32cbff6983c7573f4b60eab8b44815668130a0/python/sglang/kernels/jit/csrc/elementwise/rmsnorm.cuh).
The paper authors' adapted source and source revision are unknown. This is
intermediate evidence for an independent reproduction; it does not reproduce
the paper's original SGLang verification claim.

The selected packed double-load path supports width 16384 with 1024 threads.
The generic CTA path in this revision supports widths only through 8192.
Twelve unmodified upstream files, including helper definitions and the Apache
license, are retained under `upstream/`; `provenance.json` pins their SHA256 and
Git blob IDs. The fixed upstream logical warp width is 32 on both CUDA and HIP.
The closed adaptation embeds those groups in AMD wave64, specializes contiguous
FP16 input/output and weight, disables PDL, and scalarizes vector operations.
Rows range from 1 through 131072 with fixed fuel `(512,8,3,1)`.

The adaptation retains all input vector preloads followed by all weight
preloads, private half caches across both barriers, eight paired square
additions per thread, both five-stage XOR reductions, thirty-two separate shared
inverse slots, and conversion of all output cache cells before the final
stores. It preserves `acc + (x*x + y*y)` grouping and each logical warp's own
inverse slot. It does not replace those operations with a mathematically
equivalent reduction or reload global buffers after the barriers.

`cases/native_original` retains the selected source's unguarded
`partial[warp] = sum` writes by all 32 lanes. These produce 15872 conflicting
write pairs per row in the access model, including writes whose values may be
equal. `cases/native_fixed` explicitly adds a lane-zero guard to that one store.
This repair is separate from the original source and has no conflicting access
pairs in the finite checked launches. This finding about the independently
selected revision does not establish a defect in the paper authors' adaptation.

Current evidence:

- The complete original and repaired sources translate to 109 and 110 IR
  instructions. Six source instances bind both programs, geometry, global,
  shared and private layouts, and fixed fuel for rows 1, 3 and 131072.
- Seven Lean modules provide 36 library axiom audits and 66 source instance
  audits. They establish output coverage, unique output writers, signed address
  bounds, private half-cache bounds and thread ownership, and race freedom
  conditional on the guarded footprint. The only proof axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- Actual `execute` calls establish an original conflicting store pair and a
  guarded two-lane instruction tail **from an explicit cut state**. They do not
  establish initializer reachability, full source execution or classification
  of a whole actual trace. No complete source certificate is issued.
- Complete finite symbolic execution checks rows 1 and 3 for both variants:
  131072 output expressions and 1323648 access events in total. Independently
  indexed source-order expression DAGs agree with all outputs; read-only input
  and weight remain unchanged and all threads halt after two barriers.
- Eleven changed-source controls and eleven false Lean claims are rejected.
  Fresh source-only replay uses no Git executable or owned compiled cache;
  fourteen fully rehashed metadata controls reject unsupported proof claims
  before archive extraction.

The checked packets are in `results/components-v1`,
`results/component-validation-v1`, `results/component-stage-guards-v1`,
`results/symbolic-v1` and `results/finite-controls-v1`. These stage names preserve
their original scope when later proof stages are added. GPU execution, complete
initialized Lean execution, actual whole-trace classification, and exact-real
source/reference equality remain outstanding for this family. There have been
no model calls or GPU trials in this study.

From the repository root, with Lean/Lake 4.19.0 installed:

```sh
python3 -m unittest discover -s tests -p test_native_sglang_rmsnorm.py -v
python3 reproduction/production_sglang_rmsnorm/check_program.py \
  --output /tmp/lark-sglang-components --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/replay_components.py \
  --packet /tmp/lark-sglang-components --output /tmp/lark-sglang-replay \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/check_component_stages.py \
  --packet /tmp/lark-sglang-components --output /tmp/lark-sglang-stage-guards \
  --lean-bin /path/to/lean-4.19.0/bin
python3 reproduction/production_sglang_rmsnorm/run_symbolic.py \
  --output /tmp/lark-sglang-symbolic
python3 reproduction/production_sglang_rmsnorm/check_controls.py \
  --output /tmp/lark-sglang-finite-controls
```

Each command requires a fresh output directory. The dedicated
`native-sglang-rmsnorm` CI job reruns these gates from source.
