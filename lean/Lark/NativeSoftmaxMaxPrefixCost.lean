import Lark.NativeSoftmaxMaxPrefixReads

/-! Exact source instruction count for the first maximum prefix. -/
namespace LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem max_component_cost_early (tid iteration component : Nat)
    (ht : tid < 1024) (hi : iteration < 6) (hc : component < 8) :
    maxComponentCost tid iteration component = 8 := by
  have hb : ¬ 50257 ≤ column tid iteration component := by unfold column; omega
  simp [maxComponentCost,clampCost,hb]

theorem max_components_cost_early (tid iteration component count : Nat)
    (ht : tid < 1024) (hi : iteration < 6) (hc : component+count ≤ 8) :
    maxComponentsCost tid iteration component count = 8*count := by
  induction count generalizing component with
  | zero => simp [maxComponentsCost]
  | succ count ih =>
    simp only [maxComponentsCost]
    rewrite [max_component_cost_early tid iteration component ht hi (by omega),
      ih (component+1) (by omega)]
    omega

theorem max_round_cost_early (tid iteration : Nat) (ht : tid < 1024) (hi : iteration < 6) :
    maxRoundCost tid iteration = 69 := by
  unfold maxRoundCost
  rewrite [max_components_cost_early tid iteration 0 8 ht hi (by decide)]
  rfl

theorem max_rounds_cost_early (tid iteration count : Nat)
    (ht : tid < 1024) (hi : iteration+count ≤ 6) :
    maxRoundsCost tid iteration count = 69*count := by
  induction count generalizing iteration with
  | zero => simp [maxRoundsCost]
  | succ count ih =>
    simp only [maxRoundsCost]
    rewrite [max_round_cost_early tid iteration ht (by omega),ih (iteration+1) (by omega)]
    omega

theorem max_components_cost_last_tail (tid component count : Nat)
    (hc : 2 ≤ component) : maxComponentsCost tid 6 component count = 9*count := by
  induction count generalizing component with
  | zero => simp [maxComponentsCost]
  | succ count ih =>
    have hb : 50257 ≤ column tid 6 component := by unfold column; omega
    have head : maxComponentCost tid 6 component = 9 := by simp [maxComponentCost,clampCost,hb]
    simp only [maxComponentsCost]
    rewrite [head,ih (component+1) (by omega)]
    omega

theorem max_round_cost_last (tid : Nat) (ht : tid < 1024) :
    maxRoundCost tid 6 = if tid < 81 then 75 else 76 := by
  have zero : maxComponentCost tid 6 0 = 8 := by
    have hb : ¬ 50257 ≤ column tid 6 0 := by unfold column; omega
    simp [maxComponentCost,clampCost,hb]
  have one : maxComponentCost tid 6 1 = if tid < 81 then 8 else 9 := by
    by_cases h : tid < 81
    · have hb : ¬ 50257 ≤ column tid 6 1 := by unfold column; omega
      simp [maxComponentCost,clampCost,hb,h]
    · have hb : 50257 ≤ column tid 6 1 := by unfold column; omega
      simp [maxComponentCost,clampCost,hb,h]
  change 5 + (maxComponentCost tid 6 0 +
    (maxComponentCost tid 6 1 + maxComponentsCost tid 6 2 6)) = _
  rewrite [zero,one,max_components_cost_last_tail tid 2 6 (by decide)]
  split <;> rfl

theorem max_rounds_cost_append (tid iteration first second : Nat) :
    maxRoundsCost tid iteration (first+second) =
      maxRoundsCost tid iteration first + maxRoundsCost tid (iteration+first) second := by
  induction first generalizing iteration with
  | zero => simp [maxRoundsCost]
  | succ first ih =>
    simp only [Nat.succ_add,maxRoundsCost]
    rewrite [ih]
    rewrite [show iteration+1+first=iteration+(first+1) by omega]
    omega

theorem max_prefix_cost_exact (tid : Nat) (ht : tid < 1024) :
    maxPrefixCost tid = if tid < 81 then 497 else 498 := by
  unfold maxPrefixCost
  rewrite [show (7 : Nat)=6+1 from rfl,max_rounds_cost_append tid 0 6 1,
    max_rounds_cost_early tid 0 6 ht (by decide)]
  change 6 + (414 + (maxRoundCost tid 6 + 0)) + 2 = _
  rewrite [max_round_cost_last tid ht]
  split <;> rfl

#print axioms max_component_cost_early
#print axioms max_components_cost_early
#print axioms max_round_cost_early
#print axioms max_rounds_cost_early
#print axioms max_components_cost_last_tail
#print axioms max_round_cost_last
#print axioms max_rounds_cost_append
#print axioms max_prefix_cost_exact
end LarkNativeSoftmax
