import LarkReal.NativeAttentionSums

/-! The actual source recurrence interpreted as normalized online attention. -/
namespace LarkReal.NativeAttention
open LarkNativeAttention
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

def toAccumulator (q : QueryValue ℝ) : OnlineSoftmax.Accumulator := ⟨q.maximum, q.mass, q.stored⟩

theorem accumulator_ext (a b : OnlineSoftmax.Accumulator)
    (hm : a.m = b.m) (hl : a.l = b.l) (ho : ∀ c, a.o c = b.o c) : a = b := by
  cases a with
  | mk am al ao =>
      cases b with
      | mk bm bl bo =>
          dsimp at hm hl ho
          subst bm
          subst bl
          have hf : ao = bo := funext ho
          cases hf
          rfl

theorem first_real_step (input : Nat → Nat → ℝ) (t qi : Nat) :
    toAccumulator (onlineValues ops input 1 t qi) =
      OnlineSoftmax.start (tileMaximum ops input t qi 0) (tileEntries input t qi 0) := by
  apply accumulator_ext
  · simp [toAccumulator, onlineValues, nextQueryValue, queryScales, outputScales, scaleValues, selectedMaximum, ops, OnlineSoftmax.start]
  · simp only [toAccumulator, onlineValues, nextQueryValue, queryScales, outputScales, scaleValues]
    rw [tile_denominator_real]
    simp [selectedMaximum, selectedMass, ops, OnlineSoftmax.start]
  · intro col
    simp only [toAccumulator, onlineValues, nextQueryValue, outputValues, storedOutput, combinedOutput, oldContribution, newContribution]
    rw [tile_numerator_real]
    simp only [queryScales, outputScales, scaleValues]
    rw [tile_denominator_real]
    simp [selectedMaximum, selectedMass, ops, OnlineSoftmax.start, one_div, div_eq_mul_inv, mul_comm]

theorem next_real_step (input : Nat → Nat → ℝ) (t qi key : Nat) (old : QueryValue ℝ) (hk : key ≠ 0) :
    toAccumulator (nextQueryValue ops input t qi key old) =
      OnlineSoftmax.update (toAccumulator old) (tileMaximum ops input t qi key) (tileEntries input t qi key) := by
  apply accumulator_ext
  · simp [toAccumulator, nextQueryValue, queryScales, outputScales, scaleValues, selectedMaximum, hk, ops, OnlineSoftmax.update]
  · simp only [toAccumulator, nextQueryValue, queryScales, outputScales, scaleValues]
    rw [tile_denominator_real]
    simp [selectedMaximum, selectedMass, hk, ops, OnlineSoftmax.update]
  · intro col
    simp only [toAccumulator, nextQueryValue, outputValues, storedOutput, combinedOutput, oldContribution, newContribution]
    rw [tile_numerator_real]
    simp only [queryScales, outputScales, scaleValues]
    rw [tile_denominator_real]
    simp [selectedMaximum, selectedMass, hk, ops, OnlineSoftmax.update]

noncomputable def processedEntries (input : Nat → Nat → ℝ) (t qi n : Nat) : List OnlineSoftmax.Entry :=
  ((List.range n).map (tileEntries input t qi)).flatten

theorem processed_entries_succ (input : Nat → Nat → ℝ) (t qi n : Nat) :
    processedEntries input t qi (n + 1) = processedEntries input t qi n ++ tileEntries input t qi n := by
  simp [processedEntries, List.range_succ]

theorem online_real_valid (input : Nat → Nat → ℝ) (t qi n : Nat) :
    OnlineSoftmax.Valid (processedEntries input t qi (n + 1)) (toAccumulator (onlineValues ops input (n + 1) t qi)) := by
  induction n with
  | zero =>
      rw [first_real_step]
      simpa [processedEntries] using OnlineSoftmax.start_valid (tileEntries input t qi 0) (tileMaximum ops input t qi 0)
        (tile_entries_nonempty input t qi 0)
  | succ n ih =>
      have hs : toAccumulator (onlineValues ops input (n + 1 + 1) t qi) =
          OnlineSoftmax.update (toAccumulator (onlineValues ops input (n + 1) t qi))
            (tileMaximum ops input t qi (n + 1)) (tileEntries input t qi (n + 1)) :=
        next_real_step input t qi (n + 1) (onlineValues ops input (n + 1) t qi) (by omega)
      rw [hs, processed_entries_succ]
      exact OnlineSoftmax.update_valid _ _ _ _ ih

theorem online_mass_positive (input : Nat → Nat → ℝ) (t qi n : Nat) :
    0 < (onlineValues ops input (n + 1) t qi).mass := (online_real_valid input t qi n).1

#print axioms first_real_step
#print axioms next_real_step
#print axioms online_real_valid
#print axioms online_mass_positive
end LarkReal.NativeAttention
