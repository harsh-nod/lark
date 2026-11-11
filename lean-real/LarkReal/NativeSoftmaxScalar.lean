import Lark.NativeSoftmaxCorrect
import LarkReal.Ops

/-! Exact-real interpretation of the actual scalar exponential/sum folds.
The reserved seed has an arbitrary finite real value; both half conversions
are identities in this idealization. No IEEE interpretation is asserted. -/
namespace LarkReal.NativeSoftmax
open LarkNonlinear LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def softmaxOps (seed : ℝ) : Ops ℝ := withSeed LarkReal.ops seed

noncomputable def expTerm (input : Nat → Nat → ℝ) (row : Nat) (shift : ℝ) (col : Nat) : ℝ :=
  Real.exp (input 1 (address row col)-shift)

noncomputable def componentTerm (input : Nat → Nat → ℝ) (row tid iteration component : Nat) (shift : ℝ) : ℝ :=
  if column tid iteration component<50257 then expTerm input row shift (column tid iteration component) else 0

noncomputable def roundTerm (input : Nat → Nat → ℝ) (row tid iteration : Nat) (shift : ℝ) : ℝ :=
  ((List.range 8).map fun c => componentTerm input row tid iteration c shift).sum

theorem real_zero (seed : ℝ) : (softmaxOps seed).literal 0 1=0 := by
  simp [softmaxOps,withSeed,LarkReal.ops]

theorem store_acc_real (seed : ℝ) (input : Nat → Nat → ℝ)
    (row tid iteration component : Nat) (shift acc : ℝ) :
    expStoreAcc (softmaxOps seed) input shift acc row tid iteration component=
      acc+componentTerm input row tid iteration component shift := by
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreAcc,componentTerm,if_pos hc]
    change acc+expComponentValue (softmaxOps seed) input shift row tid iteration component=_
    rewrite [exp_component_value_in_bounds (softmaxOps seed) input shift row tid iteration component hc]
    rfl
  · simp only [expStoreAcc,componentTerm,if_neg hc,add_zero]

theorem store_fold_real (seed : ℝ) (input : Nat → Nat → ℝ)
    (row tid iteration component count : Nat) (shift acc : ℝ) :
    expStoreFold (softmaxOps seed) input shift row tid iteration component count acc=
      acc+((List.range' component count).map fun c => componentTerm input row tid iteration c shift).sum := by
  induction count generalizing component acc with
  | zero => simp [expStoreFold]
  | succ count ih =>
    simp only [expStoreFold,List.range'_succ,List.map_cons,List.sum_cons]
    rewrite [ih,store_acc_real]
    exact add_assoc _ _ _

theorem round_fold_real (seed : ℝ) (input : Nat → Nat → ℝ)
    (row tid iteration : Nat) (shift acc : ℝ) :
    expRoundFold (softmaxOps seed) input shift row tid iteration acc=acc+roundTerm input row tid iteration shift := by
  simpa only [expRoundFold,roundTerm,←List.range_eq_range'] using store_fold_real seed input row tid iteration 0 8 shift acc

theorem rounds_fold_real (seed : ℝ) (input : Nat → Nat → ℝ)
    (row tid iteration count : Nat) (shift acc : ℝ) :
    expRoundsFold (softmaxOps seed) input shift row tid iteration count acc=
      acc+((List.range' iteration count).map fun it => roundTerm input row tid it shift).sum := by
  induction count generalizing iteration acc with
  | zero => simp [expRoundsFold]
  | succ count ih =>
    simp only [expRoundsFold,List.range'_succ,List.map_cons,List.sum_cons]
    rewrite [ih,round_fold_real]
    exact add_assoc _ _ _

theorem thread_sum_real (seed : ℝ) (input : Nat → Nat → ℝ) (row tid : Nat) :
    threadExpSum (softmaxOps seed) input row tid=
      ((List.range 7).map fun it => roundTerm input row tid it (rowMaximum (softmaxOps seed) input row)).sum := by
  unfold threadExpSum
  rewrite [rounds_fold_real,real_zero,zero_add]
  rewrite [←List.range_eq_range']
  rfl

theorem norm_output_real (seed : ℝ) (input : Nat → Nat → ℝ) (row col : Nat) (hc : col<50257) :
    normOutputValue (softmaxOps seed) input row col=
      expTerm input row (rowMaximum (softmaxOps seed) input row) col/rowExpSum (softmaxOps seed) input row := by
  simp only [normOutputValue,expOutputValue,in_bounds_clamp col hc]
  rfl

#print axioms real_zero
#print axioms store_acc_real
#print axioms store_fold_real
#print axioms round_fold_real
#print axioms rounds_fold_real
#print axioms thread_sum_real
#print axioms norm_output_real
end LarkReal.NativeSoftmax
