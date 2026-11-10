# Full-wave HIP shuffle verification

This opt-in profile integrates `__shfl`, `__shfl_xor`, `__shfl_up` and
`__shfl_down` into a Lean machine. It supports float32 registers, full 64-lane
waves, blocks divisible by 64, and explicit power-of-two subgroup widths from
1 through 64. Index/XOR selectors must be smaller than the width; up/down
deltas may equal the width, with boundary lanes retaining their own value.
Partial participation, masks and tensor-core instructions are unsupported.

The whole-launch certificate proves completion, race freedom and equality to
an independent PyTorch tensor reference for every input and outside-memory
state. A shuffle reads the old register snapshot of all participating lanes,
then updates destination registers together. This handles assignments that
overwrite the source register. It changes neither memory, access traces nor
memory-order epochs; it cannot repair a memory race.

The closed reader reuses the scalar HIP frontend and rejects unsupported
forms. The new machine embeds the unchanged nonlinear scalar model.
`ShuffleTransfer.lean` proves the load/shuffle/store phases by induction, then
checks each fixture's finite lane-selection obligation in Lean. No native
evaluation axiom, admitted theorem or GPU test discharges a proof goal.

```bash
python3 -m lark_kernels verify-shuffle reproduction/shuffle/cases/reverse/kernel.hip \
  --reference reproduction/shuffle/cases/reverse/reference.py \
  --task reproduction/shuffle/cases/reverse/task.json \
  --output /tmp/lark-reverse-certificate --lean /path/to/lean
python3 -m lark_kernels check /tmp/lark-reverse-certificate --lean /path/to/lean
```

The automatic phase proof currently recognizes one-wave, five-instruction
transport kernels. Other programs within the machine's domain need explicit
proof proposals; frontend acceptance alone never issues a certificate.

[Results and evidence](RESULTS.md) cover five independent kernels and both
MI350X hosts. These are not the paper's original kernels or model outcomes.
Source lowering, scalar/collective operation correspondence, host contracts
and the external phase-reduction metatheory remain trusted. Hardware bit-copy
checks are separate finite evidence, not a proof of full GPU semantics.

To rerun the CPU study:

```bash
python3 reproduction/shuffle/run.py --output /tmp/lark-shuffle-study --lean /path/to/lean
python3 reproduction/shuffle/summarize.py --output /tmp/lark-shuffle-summary.json
```

The summary checks the archived study with its frozen source bundle, reconstructs
every immutable theorem and mutant, and audits both GPU archives. It does not
launch fresh Lean processes; use `lark check` for a fresh certificate recheck.
`prepare_gpu.py` and `run_gpu.py` create and check the separate hardware study.
