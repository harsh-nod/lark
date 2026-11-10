import Lark.Silu
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum

/-!
An optional exact-real interpretation of the unchanged nonlinear machine.
Storage conversions are identities in this idealization. This is not binary16
or binary32 arithmetic, and algebraic rearrangement here gives no error bound.
The dependency-free universally quantified certificates remain unchanged.
-/
namespace LarkReal
open LarkNonlinear

noncomputable def ops : Ops ℝ where
  literal := fun numerator denominator => (numerator : ℝ) / (denominator : ℝ)
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  max := max
  div := (· / ·)
  exp := Real.exp
  tanh := Real.tanh
  rsqrt := fun x => 1 / Real.sqrt x
  fromHalf := id
  toHalf := id

/-- The exact-real SiLU reference, with no PCs, trace, casts or source AST. -/
noncomputable def silu (x : ℝ) : ℝ := x / (1 + Real.exp (-x))

theorem silu_result (p : LarkSilu.Shape) (input : Nat → Nat → ℝ) (row col : Nat) :
    LarkSilu.result p ops input row col =
      silu (input 1 (LarkSilu.aAddress p row col)) *
        input 1 (LarkSilu.bAddress p row col) := by
  simp [LarkSilu.result, LarkSilu.activation, ops, silu]

noncomputable def siluSpec (p : LarkSilu.Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows * p.width)).map fun i =>
    silu (input 1 (LarkSilu.aAddress p (i / p.width) (i % p.width))) *
      input 1 (LarkSilu.bAddress p (i / p.width) (i % p.width))

theorem silu_spec (p : LarkSilu.Shape) : LarkSilu.spec p ops = siluSpec p := by
  funext input
  simp only [LarkSilu.spec, siluSpec, silu_result]

/-- The actual multiwave launch completes, is RF, and equals canonical real SiLU. -/
theorem silu_correct (p : LarkSilu.Shape) :
    Correct ops (LarkSilu.layout p) (LarkSilu.geometry p) (LarkSilu.fuel p)
      (LarkSilu.program p) (siluSpec p) := by
  rw [← silu_spec]
  exact LarkSilu.correct p ops

theorem fold_add (xs : List ι) (f : ι → ℝ) (start : ℝ) :
    xs.foldl (fun acc i => acc + f i) start = start + (xs.map f).sum := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

noncomputable def dotSpec (p : LarkDot.Profile) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range p.n).map fun t =>
    ((List.range p.k).map fun j =>
      input 0 (p.aAddress t j) * input 1 (p.bAddress t j)).sum

theorem dot_spec (p : LarkDot.Profile) : LarkDot.matrixSpec ops p = dotSpec p := by
  funext input
  simp [LarkDot.matrixSpec, LarkDot.dotSpec, LarkDot.term, dotSpec, ops, fold_add]

/-- Existing GEMV/matrix address profiles specialize to a canonical real dot sum. -/
theorem dot_correct (p : LarkDot.Profile) (warp : Nat)
    (hn : 0 < p.n) (hk : 0 < p.k)
    (hb : p.n < 2147483648 ∧ p.k < 2147483648) (hw : 0 < warp) :
    Correct ops (LarkDot.layout p) (LarkDot.geometry p warp) (LarkDot.fuel p)
      (LarkDot.program p) (dotSpec p) := by
  rw [← dot_spec]
  exact LarkDot.matrix_correct ops p warp hn hk hb hw

inductive AddTree where
  | leaf : Nat → AddTree
  | join : AddTree → AddTree → AddTree
  deriving Repr

def AddTree.leaves : AddTree → List Nat
  | .leaf i => [i]
  | .join left right => left.leaves ++ right.leaves

noncomputable def AddTree.eval (values : Nat → ℝ) : AddTree → ℝ
  | .leaf i => values i
  | .join left right => left.eval values + right.eval values

/-- Arbitrary binary reduction trees equal the sum of their leaves over reals. -/
theorem tree_sum (tree : AddTree) (values : Nat → ℝ) :
    tree.eval values = (tree.leaves.map values).sum := by
  induction tree with
  | leaf i => simp [AddTree.eval, AddTree.leaves]
  | join left right hl hr => simp [AddTree.eval, AddTree.leaves, hl, hr]

/-- Permuting tree leaves needs no kernel-specific arithmetic premise. -/
theorem tree_permutation (tree : AddTree) (indices : List Nat) (values : Nat → ℝ)
    (sameLeaves : tree.leaves.Perm indices) :
    tree.eval values = (indices.map values).sum := by
  rw [tree_sum]
  exact (sameLeaves.map values).sum_eq

/-- A symbolic split-K/chunking identity, with arbitrary finite chunk sizes. -/
theorem chunk_sum (chunks : List (List ℝ)) :
    (chunks.map List.sum).sum = chunks.flatten.sum := by
  induction chunks with
  | nil => rfl
  | cons xs chunks ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.sum_append, ih]

def nonassociativeOps : Ops Nat where
  literal := fun n d => n.toNat / d
  add := fun a b => a + 2 * b
  sub := Nat.sub
  mul := Nat.mul
  max := Nat.max
  div := Nat.div
  exp := id
  tanh := id
  rsqrt := id
  fromHalf := id
  toHalf := id

/-- The original universal-operations statement cannot silently assume associativity. -/
theorem universal_reassociation_impossible :
    ¬ (∀ (o : Ops Nat) (a b c : Nat), o.add (o.add a b) c = o.add a (o.add b c)) := by
  intro h
  have bad := h nonassociativeOps 1 2 3
  norm_num [nonassociativeOps] at bad

#print axioms silu_result
#print axioms silu_correct
#print axioms dot_correct
#print axioms tree_permutation
#print axioms chunk_sum
#print axioms universal_reassociation_impossible
end LarkReal
