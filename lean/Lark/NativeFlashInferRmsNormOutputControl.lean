import Lark.NativeFlashInferRmsNormOutputFrame

/-! Exact control frames needed for sequential native output-lane execution.
Every other lane retains all controls and registers; native indices are retained
for every thread, including the output lane itself.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem output_components_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u component remaining : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputComponents ops input row tid iteration t inverse component remaining s).pc u = s.pc u ∧
    (outputComponents ops input row tid iteration t inverse component remaining s).indices u = s.indices u ∧
    (outputComponents ops input row tid iteration t inverse component remaining s).regs u = s.regs u := by
  induction remaining generalizing component s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ remaining ih =>
      have h := ih (component + 1) (outputComponent ops input row tid iteration component t inverse s)
      have h1 := output_component_other ops input row tid iteration component t u inverse s hu
      exact ⟨h.1.trans h1.1,h.2.1.trans h1.2.1,h.2.2.trans h1.2.2⟩

theorem output_round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputRound ops input row tid iteration t inverse s).pc u = s.pc u ∧
    (outputRound ops input row tid iteration t inverse s).indices u = s.indices u ∧
    (outputRound ops input row tid iteration t inverse s).regs u = s.regs u := by
  have h := output_components_other ops input row tid iteration t u 0 8 inverse (outputBeginRound t s) hu
  simpa [outputRound, outputEndRound, outputBeginRound, advance, setIndex, hu] using h

theorem output_lane_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (total : α) (s : State α) (hu : u ≠ t) :
    (outputLane ops input row tid t total s).pc u = s.pc u ∧
    (outputLane ops input row tid t total s).indices u = s.indices u ∧
    (outputLane ops input row tid t total s).regs u = s.regs u := by
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  have h0 := output_entry_other ops t u row total s hu
  have h1 := output_round_other ops input row tid 0 t u inverse s0 hu
  have h2 := output_round_other ops input row tid 1 t u inverse s1 hu
  change (advance (outputRound ops input row tid 1 t inverse s1) t 67).pc u = _ ∧ _ ∧ _
  exact ⟨(by simpa only [advance, if_neg hu] using h2.1.trans (h1.1.trans h0.1)),
    h2.2.1.trans (h1.2.1.trans h0.2.1),h2.2.2.trans (h1.2.2.trans h0.2.2)⟩

theorem output_component_index_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u q : Nat) (inverse : α) (s : State α) (hq : q < 4) :
    (outputComponent ops input row tid iteration component t inverse s).indices u q = s.indices u q := by
  have h9 : q ≠ 9 := by omega
  have h10 : q ≠ 10 := by omega
  have h11 : q ≠ 11 := by omega
  simp [outputComponent, setIndex, setReg, written, record, advance, h9,h10,h11]

theorem output_components_index_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u q component remaining : Nat) (inverse : α) (s : State α) (hq : q < 4) :
    (outputComponents ops input row tid iteration t inverse component remaining s).indices u q = s.indices u q := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) (outputComponent ops input row tid iteration component t inverse s)).trans
        (output_component_index_low ops input row tid iteration component t u q inverse s hq)

theorem output_round_index_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u q : Nat) (inverse : α) (s : State α) (hq : q < 4) :
    (outputRound ops input row tid iteration t inverse s).indices u q = s.indices u q := by
  have h8 : q ≠ 8 := by omega
  have h9 : q ≠ 9 := by omega
  have h := output_components_index_low ops input row tid iteration t u q 0 8 inverse (outputBeginRound t s) hq
  simpa only [outputRound, outputEndRound, outputBeginRound, advance, setIndex,
    show ¬ (u = t ∧ q = 8) by omega, show ¬ (u = t ∧ q = 9) by omega, ↓reduceIte] using h

theorem output_lane_index_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u q : Nat) (total : α) (s : State α) (hq : q < 4) :
    (outputLane ops input row tid t total s).indices u q = s.indices u q := by
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  have h0 : s0.indices u q = s.indices u q := by
    simp [s0, outputEntered, setIndex, setReg, record, advance, show q ≠ 8 by omega]
  have h1 := output_round_index_low ops input row tid 0 t u q inverse s0 hq
  have h2 := output_round_index_low ops input row tid 1 t u q inverse s1 hq
  exact h2.trans (h1.trans h0)

theorem output_lane_native_indices (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (total : α) (s : State α) (hi : NativeIndices u s) :
    NativeIndices u (outputLane ops input row tid t total s) := by
  unfold NativeIndices at hi ⊢
  simpa only [output_lane_index_low ops input row tid t u 0 total s (by decide),
    output_lane_index_low ops input row tid t u 1 total s (by decide),
    output_lane_index_low ops input row tid t u 2 total s (by decide),
    output_lane_index_low ops input row tid t u 3 total s (by decide)] using hi

#print axioms output_components_other
#print axioms output_round_other
#print axioms output_lane_other
#print axioms output_component_index_low
#print axioms output_components_index_low
#print axioms output_round_index_low
#print axioms output_lane_index_low
#print axioms output_lane_native_indices
end LarkNativeFlashInferRmsNorm
