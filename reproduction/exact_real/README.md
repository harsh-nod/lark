# Exact-real semantics and algebra check

The [optional Lean package](../../lean-real/README.md) adds a concrete Mathlib
real interpretation of the unchanged nonlinear machine. It connects the
existing SiLU and dot-product machine proofs to canonical tensor formulas and
proves general reduction-tree/permutation and chunking identities. It also
proves that unrestricted abstract operations cannot silently be treated as
associative. This addresses a mathematical limitation in preparing optimized
reduction proofs; it is not an additional original-paper reproduction result.

The study builds the package, freshly checks `LarkReal/Ops.lean`, and requires
all six named axiom audits with only the standard three allowed axioms. A
reversed-leaf tree with a proved permutation succeeds. Duplicate and omitted
leaves fail their false permutation obligation; the nonassociative-operation
countermodel also rejects a false associativity claim. All three failures are
Lean false-decision errors with zero timeout. These algebra controls are not
the paper's original mutation experiment or GPU-kernel diagnosis channels.

A separate CPU binary32 witness rounds explicitly after each addition. For
`a=33554432`, `b=-33554432`, `c=1`, `(a+b)+c` is 1 and `a+(b+c)` is 0. This is
a finite scope example, not a theorem about floating-point error and not a GPU
measurement. The real interpretation erases storage rounding; the earlier
SiLU source certificates still preserve both half conversions and their
hardware validation still tests them. Neither theorem licenses an unbounded
IEEE rearrangement.

After the [dependency setup](../../lean-real/README.md), run:

```bash
python3 reproduction/exact_real/run.py --output /tmp/lark-exact-real
```

[results/results.json](results/results.json) records theorem audits, controls,
timings, the CPU witness and dependency commits.
[results/source-manifest.json](results/source-manifest.json) binds the 16-file
source archive, including the unchanged core libraries and the dependency lock.
[results/manifest.json](results/manifest.json) binds all raw records. Mathlib
source and compiled cache artifacts are obtained separately at the pinned
revision; they are not vendored in that small source archive.

The current runner also freezes the dependencies of the later
[wave-reduction bridge](../wave_reduction/README.md), producing a 25-file source
archive on new runs. The published original 16-file archive and counts above
remain unchanged; wave-reduction certificates and hardware trials have their
own study.

The first setup attempt reached a cache-tool native build and failed because
the local runtime-only Lean distribution has no C headers. Interpreter cache
bootstrap succeeded. The first library draft used an overly broad `simp` in
the chunk lemma and failed its recursion limit; an explicit list rewrite fixed
it. The first study controller expected different wording for Lean's negative
diagnostic and was corrected to recognize the actual false-decision message.
These unsuccessful setup/development attempts are retained separately from the
passing study. No accepted proof contains `sorryAx`.

No fresh GPU trial or model call is made. No new source certificate is counted:
the machine theorems specialize existing generic libraries. Full execution
proofs for optimized reduction kernels, packed operations, in-place aliases,
original artifacts/models and H100 results remain outstanding.
