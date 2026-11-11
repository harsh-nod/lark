import Lark.NativeAttentionCorrect
import LarkReal.Ops
import LarkReal.OnlineSoftmax

/-! Canonical real dot products and tile sums for the complete native source. -/
namespace LarkReal.NativeAttention
open LarkNativeAttention
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

theorem dot_fold_real (input : Nat → Nat → ℝ) (t qi key row start n : Nat) (acc : ℝ) :
    dotFold ops input t qi key row start n acc = acc +
      ((List.range' start n).map (fun col => input 1 (globalAddress t qi col) * input 2 (tileAddress t key row col))).sum := by
  induction n generalizing start acc with
  | zero => simp [dotFold]
  | succ n ih =>
      rw [dotFold, ih]
      simp [List.range'_succ, dotNext, dotTerm, qValue, kValue, ops, add_assoc]

theorem exp_fold_real (values : Nat → ℝ) (maximum : ℝ) (start n : Nat) (acc : ℝ) :
    expFold ops values maximum start n acc = acc + ((List.range' start n).map (fun row => Real.exp (values row - maximum))).sum := by
  induction n generalizing start acc with
  | zero => simp [expFold]
  | succ n ih =>
      rw [expFold, ih]
      simp [List.range'_succ, normalizedWeight, ops, add_assoc]

theorem pv_fold_real (input : Nat → Nat → ℝ) (t key col start n : Nat) (weights : Nat → ℝ) (acc : ℝ) :
    pvFold ops input t key col weights start n acc = acc +
      ((List.range' start n).map (fun row => weights row * input 3 (tileAddress t key row col))).sum := by
  induction n generalizing start acc with
  | zero => simp [pvFold]
  | succ n ih =>
      rw [pvFold, ih]
      simp [List.range'_succ, pvNext, pvTerm, vValue, ops, add_assoc]

def keyAddress (t row col : Nat) : Nat := t / 32 * 32768 + row * 256 + col
noncomputable def denseScore (input : Nat → Nat → ℝ) (t qi key : Nat) : ℝ :=
  ((List.range 256).map (fun col => input 1 (globalAddress t qi col) * input 2 (keyAddress t key col))).sum / 16
noncomputable def denseEntry (input : Nat → Nat → ℝ) (t qi key : Nat) : OnlineSoftmax.Entry :=
  ⟨denseScore input t qi key, fun col => input 3 (keyAddress t key col)⟩
noncomputable def tileEntries (input : Nat → Nat → ℝ) (t qi key : Nat) : List OnlineSoftmax.Entry :=
  (List.range 32).map (fun row => denseEntry input t qi (key * 32 + row))
noncomputable def denseEntries (input : Nat → Nat → ℝ) (t qi : Nat) : List OnlineSoftmax.Entry :=
  (List.range 128).map (denseEntry input t qi)

theorem tile_address_real (t key row col : Nat) : tileAddress t key row col = keyAddress t (key * 32 + row) col := by
  simp [tileAddress, keyAddress, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem score_value_real (input : Nat → Nat → ℝ) (t qi key row : Nat) :
    scoreValue ops input t qi key row = (denseEntry input t qi (key * 32 + row)).score := by
  have zero : ops.literal 0 1 = (0 : ℝ) := by simp [ops]
  have scale : ops.literal 1 16 = (1 : ℝ) / 16 := by norm_num [ops]
  unfold scoreValue rawDotValue
  rw [zero, dot_fold_real, scale]
  simp only [zero_add]
  change ((List.range' 0 256).map (fun col => input 1 (globalAddress t qi col) * input 2 (tileAddress t key row col))).sum *
    ((1 : ℝ) / 16) = denseScore input t qi (key * 32 + row)
  simp only [List.range'_eq_map_range, zero_add, List.map_id_fun, List.map_map, Function.comp_def, tile_address_real,
    denseScore, one_div, div_eq_mul_inv, one_mul]

theorem tile_denominator_real (input : Nat → Nat → ℝ) (t qi key : Nat) :
    tileDenominator ops input t qi key = OnlineSoftmax.weight (tileMaximum ops input t qi key) (tileEntries input t qi key) := by
  have zero : ops.literal 0 1 = (0 : ℝ) := by simp [ops]
  unfold tileDenominator
  rw [zero, exp_fold_real]
  simp only [zero_add, List.range'_eq_map_range, List.map_map, zero_add, Function.comp_def]
  simp only [OnlineSoftmax.weight, tileEntries, List.map_map, Function.comp_def, scoreValues, score_value_real]

theorem tile_numerator_real (input : Nat → Nat → ℝ) (t qi key col : Nat) :
    pvValue ops input t key col (rowWeightValues ops input t qi key) =
      OnlineSoftmax.numerator (tileMaximum ops input t qi key) (tileEntries input t qi key) col := by
  have zero : ops.literal 0 1 = (0 : ℝ) := by simp [ops]
  unfold pvValue
  rw [zero, pv_fold_real]
  simp only [rowWeightValues, normalizedWeight, score_value_real]
  simp only [zero_add, List.range'_eq_map_range, List.map_map, Function.comp_def, zero_add,
    OnlineSoftmax.numerator, tileEntries, denseEntry, ops, tile_address_real]

theorem tile_entries_nonempty (input : Nat → Nat → ℝ) (t qi key : Nat) : tileEntries input t qi key ≠ [] := by
  simp [tileEntries]

#print axioms dot_fold_real
#print axioms score_value_real
#print axioms tile_denominator_real
#print axioms tile_numerator_real
end LarkReal.NativeAttention
