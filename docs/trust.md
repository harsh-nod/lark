# What a certificate means

For a fixed program, tensor signature, launch geometry, and fuel, Lean checks:

```text
for every scalar type, interpretation of the scalar operations, and input,
for every initial memory outside the declared input cells:
  there exists a final machine state such that
    the launch completes without fault within the fuel,
    all conflicting cross-thread accesses are properly ordered,
    and every declared output equals the independent tensor specification.
```

`kernel_eq_spec_pre` expresses the same result for any machine state satisfying
`StdPre`. `initial_places` proves input placement and `pre_satisfiable` constructs
an initial state for every input. Outputs and scratch are not supplied as input
values; their initial contents are arbitrary, including undefined cells.

Control flow and addresses cannot depend on scalar tensor values. Consequently
the successful trace covers every input value for the fixed shape and launch.
Reads are recorded even if their value is later discarded. Read/read overlaps
are allowed; same-value write/write overlaps are still rejected.

The universally quantified `Ops` prevents the theorem from assuming convenient
arithmetic laws. It can be instantiated with exact real operations. No real
library is needed because the supported proofs preserve expression structure.
It can also be instantiated with other scalar semantics when those operations
and literals mean what the source frontend intends. No floating-point error
bound, NaN/overflow behavior, or reassociation guarantee follows from this.

`Model.lean` pins scalar-v1. `Nonlinear.lean` independently pins nonlinear-v2,
adding division, exp, tanh, reciprocal square root and explicit half conversions.
These are universally quantified functions, not an IEEE binary16 implementation.
Model selection follows the parsed program/specification and declared storage
types; rechecking derives it again and validates the selected model hash.
See the [MI350X validation](../reproduction/nonlinear/README.md) for separate
finite numerical and bit-conversion evidence. No GPU test discharges a Lean goal.

The opt-in `wave-shuffle-v13` profile embeds that unchanged nonlinear model and
adds full-wave64 snapshot register transport. Its correctness theorem still
covers actual launch completion, RF and output equality for every input and
outside-memory state. A Lean preservation lemma establishes that shuffles
change neither memory, access traces nor memory-order epochs. Source-to-HIP
operation correspondence remains trusted; the separate finite bit-copy checks
include special float32 payloads but do not establish complete hardware semantics.

The separate `wave-mfma-v14` profile adds one native AMD 16×16 half-input/float-output
matrix instruction with default modifiers. Its four logical register components
per operand and exact dot-plus-C definition remain part of the operation trust
boundary. Lean proves the actual complete tile launch against every independent
reference expression. Hardware basis-pair and exactly representable random-tile
checks provide finite evidence for the same source; they do not prove the
instruction's IEEE rounding or internal accumulation order.

## Trusted components

1. **Lean 4.19.0 and its kernel.** Each exported theorem's actual axiom
   dependencies are printed. Only `propext`, `Classical.choice`, and `Quot.sound`
   are allowed. No `sorryAx` or native-evaluation axiom is accepted.
2. **Machine and opcode semantics.** The embedded, hashed model must describe
   the intended target behavior under the exact-arithmetic abstraction. No
   complete hardware calibration has been performed here. The
   [reproduction study](../reproduction/README.md) adds finite comparisons of
   add/subtract/multiply/maximum against MI300X FP32 and numerical tests of
   selected compiled sources. These do not prove the abstract machine matches
   all hardware behavior or cover NaNs, infinities, subnormals, or rounding bounds.
3. **Python frontend and fixed lowering.** Token read-back verifies byte
   preservation, including comments and newlines. It does not prove that the
   semantic lowering is correct. This is a larger frontend trust boundary than
   the paper's Lean source lowering.
4. **Independent reference formalization.** The PyTorch AST translator is fixed
   code, but is not a verified compiler. Optional CPU tests compare the shipped
   examples against PyTorch. They provide evidence about this component.
5. **Host interface.** Named buffers have declared float32/float16 storage, are contiguous, aligned, disjoint,
   and allocated to the declared sizes. The host uses the declared launch and
   warp width. The proof covers only that interface and concrete dimensions.
6. **Phase-reduction metatheory.** As in the paper, interpreting a race-free
   sequential phase fold as every legal GPU interleaving relies on external
   reduction theory. This repository does not mechanize that theorem.

Register/index namespaces enforce the accepted subset's type separation.
Memory addresses are element-indexed; vector memory accesses and reinterpret casts
are not modeled and are refused at the source boundary. Integer arithmetic is
restricted to nonnegative signed-int32 values at every intermediate step,
avoiding signed overflow and unsigned-coordinate underflow discrepancies.

## Untrusted components

Symbolic preflight, segment proposals, proof-provider output, and generated
proof tactics cannot issue a certificate. Python proposes a concrete `traceData`
to make the finite conflict check efficient. Lean first checks that this list
is definitionally equal to the trace of the actual execution, including in the
proof over arbitrary input scalars. The fixed theorem therefore covers the
actual successful trace and execution, not just a caller-supplied footprint.
The reusable induction profiles instead prove the actual execution and its
trace invariants directly; a diagnostic `traceData` list is not a premise of
their correctness theorem.
Segmentation must flatten to the entire original program. A provider cannot
change the specification or add a kernel-specific assumption.

`lark check` regenerates the translation and fixed theorem, validates the
embedded model, and checks each artifact hash before invoking Lean. Hashes
bind the files to each other; they are not a digital signature or an
independent proof of provenance.

A standalone `lake build` proves the statement written in `Main.lean`. Use
`lark check` to additionally validate its binding to the source files. Manually
replacing an exported theorem with an unrelated theorem is not a valid source
certificate, even if the replacement compiles.

Provider commands and Lean tactic code run as local programs with the caller's
permissions. The proof-slot filter limits declarations and unchecked proof
features; it is not an operating-system security sandbox. Only execute providers
you trust to run on your machine. The default flow invokes no external provider.
