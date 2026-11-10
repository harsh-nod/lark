import Lark.NativeRmsNormOutputVectors

/-! Frames needed to compose the complete native output traversal. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_component_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t u r : Nat) (inverse : α) (s : State α) (hr : r ≠ 8) :
    (outputComponent ops input row vector component t inverse s).indices u r = s.indices u r := by
  simp [outputComponent, outputWritten, setIndex, setReg, advance, record, hr]

theorem output_components_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row vector t u r component remaining : Nat) (inverse : α) (s : State α) (hr : r ≠ 8) :
    (outputComponents ops input row vector t inverse component remaining s).indices u r = s.indices u r := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) (outputComponent ops input row vector component t inverse s)).trans
        (output_component_index_frame ops input row vector component t u r inverse s hr)

theorem output_vector_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row vector t u r : Nat) (inverse : α) (s : State α) (hr7 : r ≠ 7) (hr8 : r ≠ 8) :
    (outputVector ops input row vector t inverse s).indices u r = s.indices u r := by
  have h := output_components_index_frame ops input row vector t u r 0 8 inverse (outputBegin t s) hr8
  have ht : (outputVector ops input row vector t inverse s).indices u r =
      (outputComponents ops input row vector t inverse 0 8 (outputBegin t s)).indices u r := by
    simp [outputVector, outputTail, setIndex, advance, hr7]
  exact ht.trans (h.trans (by simp [outputBegin, setIndex, advance, hr8]))

theorem output_vector_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t u : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputVector ops input row vector t inverse s).pc u = s.pc u ∧
    (outputVector ops input row vector t inverse s).indices u = s.indices u ∧
    (outputVector ops input row vector t inverse s).regs u = s.regs u := by
  have h := output_components_other ops input row vector t u 0 8 inverse (outputBegin t s) hu
  refine ⟨?_, ?_, ?_⟩
  · exact (show (outputVector ops input row vector t inverse s).pc u =
        (outputComponents ops input row vector t inverse 0 8 (outputBegin t s)).pc u by
          simp [outputVector, outputTail, setIndex, advance, hu]).trans
      (h.1.trans (by simp [outputBegin, setIndex, advance, hu]))
  · exact (show (outputVector ops input row vector t inverse s).indices u =
        (outputComponents ops input row vector t inverse 0 8 (outputBegin t s)).indices u by
          simp [outputVector, outputTail, setIndex, advance, hu]).trans
      (h.2.1.trans (by simp [outputBegin, setIndex, advance, hu]))
  · exact h.2.2

theorem output_vector_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector t : Nat) (inverse : α) (s : State α) (l : Location)
    (hl : ∀ c, c < 8 → l ≠ globalCell 0 (scalarAddress row vector c)) :
    (outputVector ops input row vector t inverse s).memory l = s.memory l :=
  output_components_memory_other ops input row vector t 0 8 inverse (outputBegin t s) l
    (by intro c hc hb; exact hl c (by omega))

theorem scalar_vector_ne (row a b c d : Nat) (hc : c < 8) (hd : d < 8) (hab : a ≠ b) :
    globalCell 0 (scalarAddress row a c) ≠ globalCell 0 (scalarAddress row b d) := by
  intro he
  have he := congrArg Location.offset he
  simp only [globalCell, scalarAddress] at he
  omega

#print axioms output_vector_index_frame
#print axioms output_vector_other
#print axioms output_vector_memory_other
end LarkNativeRmsNorm
