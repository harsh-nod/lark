import LarkReal.NativeSglangRmsNormSum

/-! Exact-real dense weighted RMSNorm equality for the entire actual guarded
native launch. The reference uses the original input, a dense row sum and the
original weight. Storage conversions are identities in this interpretation.
-/
namespace LarkReal.NativeSglangRmsNorm
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Independent dense RMSNorm reference over the original row and weight. -/
noncomputable def canonical (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  input 1 (row*16384+col)*
    (1 / Real.sqrt ((((List.range 16384).map (rowSquare input row)).sum)/16384+1/100000))*
    input 2 col

theorem inverse_eq (input : Nat → Nat → ℝ) (row lane : Nat) (hl : lane<32) :
    blockInverseValue ops input row lane=
      1 / Real.sqrt ((((List.range 16384).map (rowSquare input row)).sum)/16384+1/100000) := by
  unfold blockInverseValue
  rw [total_from_lane input row lane hl]
  norm_num only [secondInverseValue,ops,id_eq,zero_div,zero_add,div_one]

theorem result_eq_canonical (input : Nat → Nat → ℝ) (row col : Nat) :
    sourceResult ops input row col=canonical input row col := by
  have hw : col/8%1024/32<32 := by
    have h := Nat.mod_lt (col/8) (by decide : 0<1024)
    omega
  unfold sourceResult
  rw [inverse_eq input row (col/8%1024/32) hw]
  norm_num only [ops,address,canonical,id_eq]

noncomputable def canonical_spec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows*16384)).map (fun offset => canonical input (offset/16384) (offset%16384))

theorem spec_eq (p : Shape) (input : Nat → Nat → ℝ) :
    spec p ops input=canonical_spec p input := by
  apply List.map_congr_left
  intro offset ho
  exact result_eq_canonical input (offset/16384) (offset%16384)

/-- Every supported initialized native launch completes, its actual trace is
race-free, and its full extracted output equals the independent dense real
reference for all inputs and arbitrary initial outside memory. -/
theorem correct (p : Shape) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program true) (canonical_spec p) := by
  intro input outside
  obtain ⟨final,he,hr,hv⟩ := LarkNativeSglangRmsNorm.correct p ops input outside
  exact ⟨final,he,hr,hv.trans (congrArg some (spec_eq p input))⟩

#print axioms inverse_eq
#print axioms result_eq_canonical
#print axioms spec_eq
#print axioms correct
end LarkReal.NativeSglangRmsNorm
