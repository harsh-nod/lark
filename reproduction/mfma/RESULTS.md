# Independent native MFMA results

One complete 64-lane, 16×16 half-input/float-output HIP tile has a source-bound
Lean 4.19.0 certificate and a fresh independent recheck. The actual whole-launch
theorem proves completion, race freedom and all **256 output values**, for
every input and initial outside-memory state. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`. The scalar prefix loads 768 values and
the suffix stores 256 values; the MFMA instruction adds no memory accesses
or ordering epochs.

Four controls were rejected directly by Lean without Python preflight:

| Mutation | Rejection channel |
| --- | --- |
| Wrong A row stride | Fixed-template program equality |
| Wrong B operand register | Fixed-template program equality |
| Wrong output vector component | Fixed-template program equality |
| Drop C from the independent reference | Reference equality |

There were zero accepted controls and zero timeouts. These are independent
controls, not the paper's original mutants or general diagnosis results.
The integration suite separately rejects a fully rehashed certificate whose
reference changes only output 255's C contribution. This checks the complete
output contract, including its last cell.

Both `mi350` and `mi350-2` passed **65,824 exact-source launches and 16,850,944
output-bit comparisons per host**, with zero mismatches. Every launch uses
`grid=1`, `block=64`, matching the certificate. The suite covers all 65,536
A/B basis pairs, all 256 C basis elements and 32 exactly representable integer
or dyadic random tiles. The generator separately checks 304 cases against the
independent PyTorch AST. All input bytes and each tile's 128-byte guards on
both sides of all four buffer regions remained unchanged. Captured gfx950
assembly contains the native MFMA instruction.

The primary host's first preflight found GPU 4 occupied and exited before
execution. The successful run used an idle GPU 2; the other job was left
running. The secondary host used its idle GPU 0. The failed idle check is
retained with the successful primary evidence and is not a proof rejection
or failed numerical trial.

The [raw evidence](results/) contains the source-bound certificate, mutation
statements/logs, frozen implementation, complete compressed input/output
payloads and compiler artifacts. The [summary](results/summary.json) reconstructs
all statements and regenerates every dataset byte before checking both GPU
archives. The [validation record](results/validation.json) binds the archives
and validation logs by SHA-256. A package-wheel check also reverified the
certificate outside the source checkout.

This is an independent implementation of one AMD instruction tile. It does
not reproduce the authors' optimized or production kernels, larger tiled
launches, combinations of collectives, other MFMA forms/modifiers, NVIDIA
operations, original model outcomes or IEEE rounding behavior. The earlier
[MFMA layout probes](../collective_conformance/RESULTS.md) remain a separate
hardware study; these new counts are not added to the full-shape workload ledger.
