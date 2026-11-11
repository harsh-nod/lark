import Lark.NativeSoftmaxNormLane

/-! Exact normalization scalar-step and access counts. Valid columns use the
same ownership partition as the proved exponential pass. The repaired source
skips invalid loads, while the original performs an unused clamped read/store. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_stores_count_exp (tid iteration component count : Nat) :
    normStoresCount tid iteration component count=expStoresCount tid iteration component count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih => simp only [normStoresCount,expStoresCount,ih]

theorem norm_loads_count_fixed (tid iteration component count : Nat) :
    normLoadsCount true tid iteration component count=expStoresCount tid iteration component count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih => simp [normLoadsCount,expStoresCount,ih]

theorem norm_loads_count_original (tid iteration component count : Nat) : normLoadsCount false tid iteration component count=count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih => simp [normLoadsCount,ih,Nat.add_comm]

theorem norm_load_cost_fixed (col : Nat) : normLoadCost true col=(if col<50257 then 7 else 5) := by
  by_cases hc : col<50257 <;> simp [normLoadCost,normChoiceCost,hc]

theorem norm_load_cost_original (col : Nat) : normLoadCost false col=(if col<50257 then 7 else 8) := by
  by_cases hc : col<50257
  · simp [normLoadCost,normChoiceCost,clampCost,hc,show ¬50257≤col by omega]
  · simp [normLoadCost,normChoiceCost,clampCost,hc,show 50257≤col by omega]

theorem norm_stores_cost_count (tid iteration component count : Nat) :
    normStoresCost tid iteration component count=5*count+3*expStoresCount tid iteration component count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih =>
    simp only [normStoresCost,normStoreCost,expStoresCount,ih]
    split <;> omega

theorem norm_loads_cost_fixed (tid iteration component count : Nat) :
    normLoadsCost true tid iteration component count=5*count+2*expStoresCount tid iteration component count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih =>
    simp only [normLoadsCost,norm_load_cost_fixed,expStoresCount,ih]
    split <;> omega

theorem norm_loads_cost_original (tid iteration component count : Nat) :
    normLoadsCost false tid iteration component count+expStoresCount tid iteration component count=8*count := by
  induction count generalizing component with
  | zero => rfl
  | succ count ih =>
    have tail := ih (component+1)
    simp only [normLoadsCost,norm_load_cost_original,expStoresCount]
    split <;> omega

theorem norm_round_cost_fixed (tid iteration : Nat) : normRoundCost true tid iteration=87+5*expStoresCount tid iteration 0 8 := by
  simp only [normRoundCost,normBufferCost,norm_loads_cost_fixed,norm_stores_cost_count]
  omega

theorem norm_round_cost_original (tid iteration : Nat) : normRoundCost false tid iteration=111+2*expStoresCount tid iteration 0 8 := by
  have h := norm_loads_cost_original tid iteration 0 8
  simp only [normRoundCost,normBufferCost,norm_stores_cost_count]
  omega

theorem norm_rounds_cost_fixed (tid iteration count : Nat) :
    normRoundsCost true tid iteration count=87*count+5*expRoundsCount tid iteration count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    simp only [normRoundsCost,norm_round_cost_fixed,expRoundsCount,ih]
    omega

theorem norm_rounds_cost_original (tid iteration count : Nat) :
    normRoundsCost false tid iteration count=111*count+2*expRoundsCount tid iteration count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    simp only [normRoundsCost,norm_round_cost_original,expRoundsCount,ih]
    omega

theorem norm_rounds_count_fixed (tid iteration count : Nat) : normRoundsCount true tid iteration count=2*expRoundsCount tid iteration count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    simp only [normRoundsCount,norm_loads_count_fixed,norm_stores_count_exp,expRoundsCount,ih]
    omega

theorem norm_rounds_count_original (tid iteration count : Nat) : normRoundsCount false tid iteration count=8*count+expRoundsCount tid iteration count := by
  induction count generalizing iteration with
  | zero => rfl
  | succ count ih =>
    simp only [normRoundsCount,norm_loads_count_original,norm_stores_count_exp,expRoundsCount,ih]
    omega

theorem norm_lane_cost_exact (guarded : Bool) (tid : Nat) (ht : tid<1024) :
    normLaneCost guarded tid=(if guarded then (if tid<81 then 862 else 857) else (if tid<81 then 880 else 878)) := by
  cases guarded <;> rewrite [normLaneCost]
  · rewrite [norm_rounds_cost_original,exp_rounds_count_exact tid ht]
    by_cases h : tid<81 <;> simp [h]
  · rewrite [norm_rounds_cost_fixed,exp_rounds_count_exact tid ht]
    by_cases h : tid<81 <;> simp [h]

theorem norm_lane_trace_exact (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (normLaneState guarded ops input row tid s).trace.length=s.trace.length+
      (if guarded then (if tid<81 then 201 else 197) else (if tid<81 then 213 else 211)) := by
  rewrite [norm_lane_trace_length]
  cases guarded
  · rewrite [norm_rounds_count_original,exp_rounds_count_exact tid ht]
    by_cases h : tid<81 <;> simp [h] <;> omega
  · rewrite [norm_rounds_count_fixed,exp_rounds_count_exact tid ht]
    by_cases h : tid<81 <;> simp [h] <;> omega

#print axioms norm_stores_count_exp
#print axioms norm_loads_count_fixed
#print axioms norm_loads_count_original
#print axioms norm_load_cost_fixed
#print axioms norm_load_cost_original
#print axioms norm_stores_cost_count
#print axioms norm_loads_cost_fixed
#print axioms norm_loads_cost_original
#print axioms norm_round_cost_fixed
#print axioms norm_round_cost_original
#print axioms norm_rounds_cost_fixed
#print axioms norm_rounds_cost_original
#print axioms norm_rounds_count_fixed
#print axioms norm_rounds_count_original
#print axioms norm_lane_cost_exact
#print axioms norm_lane_trace_exact
end LarkNativeSoftmax
