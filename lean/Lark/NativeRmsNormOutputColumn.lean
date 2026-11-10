import Lark.NativeRmsNormOutputOwnership

/-! Join the actual owned output stores to the independent source-tree target. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_weighted_result (ops : Ops α) (input : Nat → Nat → α) (row vector c : Nat) :
    ops.toHalf (outputWeighted ops input row vector c (scale ops input row)) = result ops input row (vector * 8 + c) := by
  simp only [outputWeighted, result, scalarAddress, Nat.add_assoc]

theorem output_lane_vector_value (ops : Ops α) (input : Nat → Nat → α)
    (row tid t vector c : Nat) (s : State α) (hv : vector < 2048) (hc : c < 8) (hm : vector % 1024 = tid) :
    (outputLane ops input row tid t s).memory (globalCell 0 (scalarAddress row vector c)) =
      some (result ops input row (vector * 8 + c)) := by
  by_cases hlt : vector < 1024
  · have he : tid = vector := by simpa only [Nat.mod_eq_of_lt hlt] using hm.symm
    clear hm
    subst tid
    exact (output_lane_value ops input row vector t c s hc).1.trans
      (congrArg some (output_weighted_result ops input row vector c))
  · have he : vector = tid + 1024 := by
      have hd := Nat.div_add_mod vector 1024
      omega
    clear hm
    subst vector
    exact (output_lane_value ops input row tid t c s hc).2.trans
      (congrArg some (output_weighted_result ops input row (tid + 1024) c))

theorem output_lane_column_value (ops : Ops α) (input : Nat → Nat → α)
    (row t col : Nat) (s : State α) (hc : col < 16384) :
    (outputLane ops input row (col / 8 % 1024) t s).memory (globalCell 0 (row * 16384 + col)) =
      some (result ops input row col) := by
  have hv : col / 8 < 2048 := by omega
  have hm : col % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : col / 8 * 8 + col % 8 = col := by have h := Nat.div_add_mod col 8; omega
  have h := output_lane_vector_value ops input row (col / 8 % 1024) t (col / 8) (col % 8) s hv hm rfl
  have ha : globalCell 0 (scalarAddress row (col / 8) (col % 8)) = globalCell 0 (row * 16384 + col) := by
    apply congrArg (globalCell 0)
    unfold scalarAddress
    omega
  have hx : result ops input row (col / 8 * 8 + col % 8) = result ops input row col := congrArg (result ops input row) he
  exact (congrArg (fun l => (outputLane ops input row (col / 8 % 1024) t s).memory l) ha).symm.trans
    (h.trans (congrArg some hx))

#print axioms output_lane_column_value
end LarkNativeRmsNorm
