import LarkReal.NativeSoftmaxSum
import Mathlib.Tactic.Ring

/-! Canonical exact-real softmax for the actual complete repaired source
launch. The finite seed is arbitrary: its normalization shift cancels. Half
casts are identities here; this theorem asserts no IEEE equality or error
bound and does not interpret the source's -infinity sentinel as a real. -/
namespace LarkReal.NativeSoftmax
open LarkNonlinear LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def canonicalOutput (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  Real.exp (input 1 (address row col))/
    ((List.range 50257).map fun c => Real.exp (input 1 (address row c))).sum

noncomputable def canonicalSpec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows*50257)).map fun offset => canonicalOutput input (offset/50257) (offset%50257)

theorem exp_term_scale (input : Nat → Nat → ℝ) (row col : Nat) (shift : ℝ) :
    Real.exp shift*expTerm input row shift col=Real.exp (input 1 (address row col)) := by
  unfold expTerm
  rewrite [←Real.exp_add]
  congr 1
  ring

theorem exp_sum_scale (input : Nat → Nat → ℝ) (row : Nat) (xs : List Nat) (shift : ℝ) :
    Real.exp shift*(xs.map (expTerm input row shift)).sum=
      (xs.map fun col => Real.exp (input 1 (address row col))).sum := by
  induction xs with
  | nil => simp
  | cons col xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rewrite [mul_add,exp_term_scale,ih]
    rfl

theorem exp_sum_nonneg (input : Nat → Nat → ℝ) (row : Nat) (xs : List Nat) (shift : ℝ) :
    0≤(xs.map (expTerm input row shift)).sum := by
  induction xs with
  | nil => simp
  | cons col xs ih => exact add_nonneg (Real.exp_pos _).le ih

theorem exp_sum_pos (input : Nat → Nat → ℝ) (row : Nat) (xs : List Nat) (shift : ℝ) (hne : xs≠[]) :
    0<(xs.map (expTerm input row shift)).sum := by
  cases xs with
  | nil => contradiction
  | cons col xs => exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (exp_sum_nonneg input row xs shift)

theorem source_denominator_pos (seed : ℝ) (input : Nat → Nat → ℝ) (row : Nat) :
    0<rowExpSum (softmaxOps seed) input row := by
  rewrite [row_sum_exponentials]
  apply exp_sum_pos input row (List.range 50257) (rowMaximum (softmaxOps seed) input row)
  intro he
  have hl := congrArg List.length he
  simp only [List.length_range,List.length_nil] at hl
  omega

theorem source_output_canonical (seed : ℝ) (input : Nat → Nat → ℝ) (row col : Nat) (hc : col<50257) :
    normOutputValue (softmaxOps seed) input row col=canonicalOutput input row col := by
  rewrite [norm_output_real seed input row col hc,row_sum_exponentials]
  unfold canonicalOutput
  let shift := rowMaximum (softmaxOps seed) input row
  rewrite [←exp_term_scale input row col shift,←exp_sum_scale input row (List.range 50257) shift]
  exact (mul_div_mul_left _ _ (Real.exp_pos shift).ne').symm

theorem source_spec_canonical (p : Shape) (seed : ℝ) :
    sourceOrderedSpec p (softmaxOps seed)=canonicalSpec p := by
  funext input
  unfold sourceOrderedSpec canonicalSpec
  apply List.map_congr_left
  intro offset ho
  exact source_output_canonical seed input (offset/50257) (offset%50257) (Nat.mod_lt _ (by decide))

/-- Actual source execution, race freedom and extraction for every supported
shape and all real inputs, against the independent dense softmax formula. -/
theorem canonical_correct (p : Shape) (seed : ℝ) :
    LarkPartitionCollective.Correct (softmaxOps seed) (layout p) (geometry p) fuel (program true) (canonicalSpec p) := by
  rewrite [←source_spec_canonical p seed]
  exact source_order_correct p (softmaxOps seed)

#print axioms exp_term_scale
#print axioms exp_sum_scale
#print axioms exp_sum_nonneg
#print axioms exp_sum_pos
#print axioms source_denominator_pos
#print axioms source_output_canonical
#print axioms source_spec_canonical
#print axioms canonical_correct
end LarkReal.NativeSoftmax
