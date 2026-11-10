# Native attention execution prefix

`Lark.NativeAttentionFirstLane` proves execution of the unchanged pinned
91-instruction native FP16 program from PC 0 to the first block barrier at
PC 20. This is a partial execution theorem, with **zero new whole-source
certificates** and no new claim of reproducing an original paper experiment.

The theorem quantifies over every permitted group count (`1..65535`), every
active lane, every scalar type and operation interpretation, every input and
every initial outside-memory value. It assumes that the lane starts at PC 0
and that the declared input cells contain that input. The original machine's
`runLane`, native block32/wave64 geometry and one-million-instruction lane fuel
are unchanged.

The checked prefix executes 5,405 scalar source instructions: the three index
setup instructions, 4,118 output-initialization instructions and 1,284 first-tile
copy instructions. It then parks at PC 20. Each lane's 1,024 output cells contain
`ops.toHalf (ops.literal 0 1)`; its 256 K cells and 256 V cells contain the
corresponding `ops.fromHalf` input values. Every input remains unchanged.
The proof retains explicit half conversions and assumes no IEEE identities.

Given a trace already satisfying the local access conditions and an even block
epoch, every access added by this prefix satisfies those conditions. The actual
machine's race check therefore accepts the resulting prefix trace. Empty launch
traces and epoch zero meet these premises. Scheduling all 32 lanes together and
resuming their barrier are outside this lane-only checkpoint. The later
[block checkpoint](BLOCK.md) now supplies those composition and resumption proofs.

The public statements are:

- `first_lane_eq`: the actual 5,405-instruction execution reduction.
- `first_lane_run`: actual execution with the pinned lane fuel returns the prefix state.
- `first_lane_output`, `first_lane_tile`: all lane-owned zero outputs and first K/V rows.
- `first_lane_reads`: preservation of all declared input cells.
- `first_lane_good`, `first_lane_race_free`: actual prefix-trace classification and race check.

The [frozen checkpoint](results/native-prefix-v1/results.json) rebuilds the closed
Lean source project outside Git, checks freshly translated source/layout identity,
audits the seven main theorem dependencies and rejects three false postconditions:
the wrong barrier PC, a nonzero initialized output and an incorrect copied key.
These controls check this prefix; they are not the paper's mutation benchmark.
Its `source.tar.gz` contains the complete local Lean import closure and source
binding. With Lean 4.19.0, extract it and run `lake build` and `lake env lean Main.lean`.
The three other top-level Lean files intentionally fail at false assertions.

```bash
python3 reproduction/online_attention/check_native_prefix.py --output /tmp/native-prefix
```

This checkpoint adds no GPU or model calls. The HIP source is byte-identical to
the [earlier paired MI350 validation](NATIVE.md). It does not prove barrier
resumption, later K/V tiles, score/softmax/output computation, whole-launch
race freedom, canonical dense-reference equality or a floating-point error bound.
