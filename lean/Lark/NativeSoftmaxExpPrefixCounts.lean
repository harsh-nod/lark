import Lark.NativeSoftmaxExpPrefix

/-! Exact source counts, composed from the six fully valid rounds and the
final partial round. No execution fuel or proof limits are increased. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exp_stores_count_all (tid iteration component count : Nat)
    (h : ∀ slot, component≤slot → slot<component+count → column tid iteration slot<50257) :
    expStoresCount tid iteration component count=count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih =>
    have head := h component (by omega) (by omega)
    have tail := ih (component+1) (by intro slot hlo hhi; exact h slot (by omega) (by omega))
    simp only [expStoresCount,if_pos head,tail]
    omega

theorem exp_load_cost_indicator (tid iteration component : Nat) :
    expLoadCost tid iteration component=(if column tid iteration component<50257 then 7 else 8) := by
  by_cases hc : column tid iteration component<50257
  · simp only [expLoadCost,clampCost,if_pos hc,if_neg (show ¬50257≤column tid iteration component by omega)]
  · simp only [expLoadCost,clampCost,if_neg hc,if_pos (show 50257≤column tid iteration component by omega)]

theorem exp_loads_cost_all (tid iteration component count : Nat)
    (h : ∀ slot, component≤slot → slot<component+count → column tid iteration slot<50257) :
    expLoadsCost tid iteration component count=7*count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih =>
    have head := h component (by omega) (by omega)
    have tail := ih (component+1) (by intro slot hlo hhi; exact h slot (by omega) (by omega))
    simp only [expLoadsCost,exp_load_cost_indicator,if_pos head,tail]
    omega

theorem exp_early_column (tid iteration component : Nat) (ht : tid<1024) (hi : iteration<6) (hc : component<8) :
    column tid iteration component<50257 := by unfold column; omega

theorem exp_early_round_count (tid iteration : Nat) (ht : tid<1024) (hi : iteration<6) :
    expStoresCount tid iteration 0 8=8 :=
  exp_stores_count_all tid iteration 0 8 (by intro slot _ hs; exact exp_early_column tid iteration slot ht hi hs)

theorem exp_early_round_cost (tid iteration : Nat) (ht : tid<1024) (hi : iteration<6) :
    expRoundCost tid iteration=143 := by
  have loads := exp_loads_cost_all tid iteration 0 8 (by intro slot _ hs; exact exp_early_column tid iteration slot ht hi hs)
  have stores := exp_early_round_count tid iteration ht hi
  simp only [expRoundCost,expBufferCost,loads,exp_stores_cost_count,stores]

theorem exp_early_rounds_count (tid iteration count : Nat) (ht : tid<1024) (hi : iteration+count≤6) :
    expRoundsCount tid iteration count=8*count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    have head := exp_early_round_count tid iteration ht (by omega)
    have tail := ih (iteration+1) (by omega)
    simp only [expRoundsCount,head,tail]
    omega

theorem exp_early_rounds_cost (tid iteration count : Nat) (ht : tid<1024) (hi : iteration+count≤6) :
    expRoundsCost tid iteration count=143*count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    have head := exp_early_round_cost tid iteration ht (by omega)
    have tail := ih (iteration+1) (by omega)
    simp only [expRoundsCost,head,tail]
    omega

theorem exp_rounds_count_append (tid iteration first second : Nat) :
    expRoundsCount tid iteration (first+second)=expRoundsCount tid iteration first+expRoundsCount tid (iteration+first) second := by
  induction first generalizing iteration with
  | zero => simp [expRoundsCount]
  | succ first ih =>
    have h : first+1+second=(first+second)+1 := by omega
    rewrite [h]
    simp only [expRoundsCount]
    rewrite [ih]
    have hi : iteration+1+first=iteration+(first+1) := by omega
    rewrite [hi]
    omega

theorem exp_rounds_cost_append (tid iteration first second : Nat) :
    expRoundsCost tid iteration (first+second)=expRoundsCost tid iteration first+expRoundsCost tid (iteration+first) second := by
  induction first generalizing iteration with
  | zero => simp [expRoundsCost]
  | succ first ih =>
    have h : first+1+second=(first+second)+1 := by omega
    rewrite [h]
    simp only [expRoundsCost]
    rewrite [ih]
    have hi : iteration+1+first=iteration+(first+1) := by omega
    rewrite [hi]
    omega

theorem exp_last_column (tid component : Nat) (ht : tid<1024) (hc : component<8) :
    (column tid 6 component<50257) ↔ component=0 ∨ (component=1 ∧ tid<81) := by unfold column; omega

theorem exp_last_round_count (tid : Nat) (ht : tid<1024) :
    expStoresCount tid 6 0 8=(if tid<81 then 2 else 1) := by
  by_cases h : tid<81 <;>
    simp [expStoresCount,exp_last_column tid 0 ht (by decide),exp_last_column tid 1 ht (by decide),
      exp_last_column tid 2 ht (by decide),exp_last_column tid 3 ht (by decide),exp_last_column tid 4 ht (by decide),
      exp_last_column tid 5 ht (by decide),exp_last_column tid 6 ht (by decide),exp_last_column tid 7 ht (by decide),h]

theorem exp_last_loads_cost (tid : Nat) (ht : tid<1024) :
    expLoadsCost tid 6 0 8=(if tid<81 then 62 else 63) := by
  by_cases h : tid<81 <;>
    simp [expLoadsCost,exp_load_cost_indicator,exp_last_column tid 0 ht (by decide),exp_last_column tid 1 ht (by decide),
      exp_last_column tid 2 ht (by decide),exp_last_column tid 3 ht (by decide),exp_last_column tid 4 ht (by decide),
      exp_last_column tid 5 ht (by decide),exp_last_column tid 6 ht (by decide),exp_last_column tid 7 ht (by decide),h]

theorem exp_last_round_cost (tid : Nat) (ht : tid<1024) : expRoundCost tid 6=(if tid<81 then 119 else 115) := by
  rewrite [expRoundCost,expBufferCost,exp_last_loads_cost tid ht,exp_stores_cost_count,exp_last_round_count tid ht]
  by_cases h : tid<81 <;> simp [h]

theorem exp_rounds_count_exact (tid : Nat) (ht : tid<1024) :
    expRoundsCount tid 0 7=(if tid<81 then 50 else 49) := by
  have h := exp_rounds_count_append tid 0 6 1
  rewrite [exp_early_rounds_count tid 0 6 ht (by decide)] at h
  change expRoundsCount tid 0 7=8*6+(expStoresCount tid 6 0 8+0) at h
  rewrite [exp_last_round_count tid ht] at h
  rewrite [h]
  by_cases hb : tid<81 <;> simp [hb]

theorem exp_prefix_cost_exact (tid : Nat) (ht : tid<1024) : expPrefixCost tid=(if tid<81 then 982 else 978) := by
  have h := exp_rounds_cost_append tid 0 6 1
  rewrite [exp_early_rounds_cost tid 0 6 ht (by decide)] at h
  change expRoundsCost tid 0 7=143*6+(expRoundCost tid 6+0) at h
  rewrite [exp_last_round_cost tid ht] at h
  unfold expPrefixCost
  rewrite [h]
  by_cases hb : tid<81 <;> simp [hb]

theorem exp_prefix_trace_exact (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) (ht : tid<1024) :
    (expPrefixState ops input row tid s).trace.length=s.trace.length+(if tid<81 then 213 else 211) := by
  rewrite [exp_prefix_trace_length,exp_rounds_count_exact tid ht]
  by_cases h : tid<81 <;> simp only [h,↓reduceIte] <;> omega

#print axioms exp_stores_count_all
#print axioms exp_load_cost_indicator
#print axioms exp_loads_cost_all
#print axioms exp_early_column
#print axioms exp_early_round_count
#print axioms exp_early_round_cost
#print axioms exp_early_rounds_count
#print axioms exp_early_rounds_cost
#print axioms exp_rounds_count_append
#print axioms exp_rounds_cost_append
#print axioms exp_last_column
#print axioms exp_last_round_count
#print axioms exp_last_loads_cost
#print axioms exp_last_round_cost
#print axioms exp_rounds_count_exact
#print axioms exp_prefix_cost_exact
#print axioms exp_prefix_trace_exact
end LarkNativeSoftmax
