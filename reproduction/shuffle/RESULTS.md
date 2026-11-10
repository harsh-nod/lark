# Independent full-wave shuffle results

Five source-bound float32 HIP certificates verified and independently rechecked
with Lean 4.19.0. All use one block of 64 lanes:

| Kernel | Independent tensor reference | Proof result |
| --- | --- | --- |
| Reverse wave | Flip the 64-element input | Verified and rechecked |
| Broadcast within width 8 | Repeat subgroup column 1 | Verified and rechecked |
| XOR within width 8 | Swap neighboring column pairs | Verified and rechecked |
| Up within width 8 | Shift columns up, retaining each first lane | Verified and rechecked |
| Down within width 8 | Shift columns down, retaining each last lane | Verified and rechecked |

The actual whole-launch theorem includes completion, race freedom and output
equality for arbitrary inputs/outside memory. Its only axioms are Lean's
standard `propext`, `Classical.choice` and `Quot.sound`. Each launch records
64 input reads and 64 output writes. The reusable phase proof avoids reducing
the entire register-update fold independently for every lane.

Four mutations were rejected directly by Lean, bypassing Python preflight:
wrong broadcast selector, wrong XOR mask, wrong up/down direction and an invalid
source-lane expression. There were zero accepted mutants and zero timeouts.
These four controls are not the authors' original mutants. Additional tests
check lossless source readback, in-place register updates, wave isolation,
invalid participation, unsupported forms and source-binding forgery. A scratch
memory example confirms that a shuffle leaves a cross-lane race unordered;
adding a block barrier repairs that example in the executable machine.

Both `mi350` and `mi350-2` passed **50 exact-source trials and 3,200 output-bit
comparisons per host**, with zero mismatches. Input payloads and 128-byte guard
zones on both sides of both allocations remained unchanged. Ten input sets
include zero, signed zero, subnormals, infinities, NaN payloads and deterministic
random uint32 payloads. The HIP compiler includes the same five kernel files
that the certificates bind; no kernel rewrite is substituted for execution.
This is bit-copy validation, not arithmetic or IEEE error-bound verification.

These results extend an independent implementation. They do not reproduce
the paper's original optimized kernels, partial-mask behavior, NVIDIA
operations, tensor-core integration or model pass-rate results. The earlier
[shuffle/MFMA conformance study](../collective_conformance/RESULTS.md) remains
separate; its MFMA layout probes do not become formal MFMA certificates here.

Raw proofs, failed mutations, logs, source snapshot, dataset and both hardware
archives are under [results](results/). [summary.json](results/summary.json)
is reconstructed from the frozen sources and raw evidence;
[validation.json](results/validation.json) records archive and validation hashes.
