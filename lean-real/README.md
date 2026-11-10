# Optional exact-real semantics

This separate Lean package instantiates the unchanged nonlinear machine over
Mathlib's `ℝ`. Addition, multiplication, division, maximum, exponential, tanh
and reciprocal square root have their ordinary real meanings. Literals are
exact rational casts. Both half conversions are identities in this explicit
idealization. Division uses Mathlib's totalized real division, including at
zero; this package introduces no claim about GPU exceptions or IEEE behavior.

`LarkReal.silu_correct` specializes the existing whole multiwave launch proof
and proves that its output is canonical `x / (1 + exp (-x)) * y` at every cell.
`LarkReal.dot_correct` specializes the existing dot-product address profiles and
replaces their operational left fold with the canonical sum of real products.
Both retain actual machine completion, race freedom, every input and arbitrary
initial outside memory. Their existing shape, address and host contracts apply.

The generic tree theorem equates any binary addition tree with the sum of its
leaves; a proved permutation then permits reordering. The chunking theorem
allows arbitrary finite chunk lengths. These are algebraic lemmas for future
optimized reduction proofs. They do **not** prove that an arbitrary shuffle,
packed or tiled GPU program implements the tree or its claimed leaves. That
machine-execution and footprint proof must still be supplied per program.

The [full-wave reduction profile](../reproduction/wave_reduction/README.md)
supplies those machine proofs for one sixteen-instruction native wave64 XOR
butterfly. `LarkReal.WaveSum.correct` proves all 64 outputs equal the canonical
real sum. The source-bound `verify-wave-sum` / `lark check` profile validates
that exact program and all independently translated reference cells. Its
separate AMD experiment records ordinary numerical agreement and cancellation
disagreements; no floating-point equality or error theorem is claimed.

The original certificates quantify over unrestricted `Ops`. This is stronger
than an exact-real theorem for programs preserving expression order, and it
cannot justify associativity silently: `universal_reassociation_impossible`
proves a concrete counterexample. This package supplies a real interpretation
without changing that original statement or adding an arithmetic axiom.

Mathlib is pinned to v4.19.0 commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lake-manifest.json](lake-manifest.json)
also pins its transitive dependencies. Lean remains 4.19.0. Only `propext`,
`Classical.choice` and `Quot.sound` occur in the printed theorem audits. The
default Python package and earlier standalone exports remain dependency free.
The optional real wave-sum profile requires the pinned Mathlib dependency/cache.

With a full Lean installation, fetch the pinned dependencies and selected cache:

```bash
cd lean-real
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Data.Complex.Trigonometric \
  Mathlib.Analysis.SpecialFunctions.Sqrt \
  Mathlib.Algebra.BigOperators.Group.List.Basic Mathlib.Tactic.NormNum Mathlib.Data.Nat.Bitwise
lake build
lake env lean LarkReal/Ops.lean
cd ..
python3 reproduction/exact_real/run.py --output /tmp/lark-exact-real
```

A runtime-only Lean distribution without C headers/static libraries can run the
cache tool through the interpreter after `lake build +Cache.Main:olean`:

```bash
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get \
  Mathlib.Data.Complex.Trigonometric Mathlib.Analysis.SpecialFunctions.Sqrt \
  Mathlib.Algebra.BigOperators.Group.List.Basic Mathlib.Tactic.NormNum Mathlib.Data.Nat.Bitwise
```

The [recorded study](../reproduction/exact_real/README.md) separately checks a
positive leaf-permutation control, rejects three false algebra obligations,
and records a CPU binary32 example where reassociation changes the answer.
That earlier algebra study adds no GPU certificate or trial. The separate
wave-reduction study records its own certificate and hardware evidence.
