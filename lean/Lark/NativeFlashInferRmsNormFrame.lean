import Lark.NativeFlashInferRmsNormPrefix

/-! Other-thread and stable-index frames for read-only scalar preparation. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem component_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t q : Nat) (acc : α) (s : State α)
    (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (componentAfter ops input row tid iteration component t acc s).indices t q = s.indices t q := by
  simp [componentAfter, setIndex, setReg, written, record, advance, h5, h6, h7]


theorem components_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (components ops input row tid iteration t component remaining acc s).pc u = s.pc u ∧
    (components ops input row tid iteration t component remaining acc s).indices u = s.indices u ∧
    (components ops input row tid iteration t component remaining acc s).regs u = s.regs u := by
  induction remaining generalizing component acc s with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)
      have hc := component_other ops input row tid iteration component t u acc s hu
      exact ⟨h.1.trans hc.1, h.2.1.trans hc.2.1, h.2.2.trans hc.2.2⟩


theorem components_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining q : Nat) (acc : α) (s : State α)
    (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (components ops input row tid iteration t component remaining acc s).indices t q = s.indices t q := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) _ _).trans
        (component_index_frame ops input row tid iteration component t q acc s h5 h6 h7)


theorem round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (roundAfter ops input row tid iteration t acc s).pc u = s.pc u ∧
    (roundAfter ops input row tid iteration t acc s).indices u = s.indices u ∧
    (roundAfter ops input row tid iteration t acc s).regs u = s.regs u := by
  have h := components_other ops input row tid iteration t 0 8 u acc (beginRound t s) hu
  simpa only [roundAfter, endRound, beginRound, setIndex, advance, if_neg hu,
    hu, false_and, ↓reduceIte] using h


theorem round_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t q : Nat) (acc : α) (s : State α)
    (h4 : q ≠ 4) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (roundAfter ops input row tid iteration t acc s).indices t q = s.indices t q := by
  have h := components_index_frame ops input row tid iteration t 0 8 q acc (beginRound t s) h5 h6 h7
  simpa only [roundAfter, endRound, beginRound, setIndex, advance, h4, h5,
    and_false, ↓reduceIte] using h

theorem initialized_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    (initialized ops t s).pc u = s.pc u ∧
    (initialized ops t s).indices u = s.indices u ∧ (initialized ops t s).regs u = s.regs u := by
  simp [initialized, indexedAt, setIndex, setReg, advance, hu]

theorem prefix_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    (prefixState ops input t s).pc u = s.pc u ∧
    (prefixState ops input t s).indices u = s.indices u ∧ (prefixState ops input t s).regs u = s.regs u := by
  have h0 := initialized_other ops t u s hu
  have h1 := round_other ops input (t / 1024) (t % 1024) 0 t u (ops.literal 0 1) (initialized ops t s) hu
  have h2 := round_other ops input (t / 1024) (t % 1024) 1 t u
    (folded ops input (t / 1024) (t % 1024) 0 0 8 (ops.literal 0 1))
    (roundAfter ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1) (initialized ops t s)) hu
  refine ⟨?_, h2.2.1.trans (h1.2.1.trans h0.2.1), h2.2.2.trans (h1.2.2.trans h0.2.2)⟩
  simpa only [prefixState, beforeShuffle, advance, if_neg hu] using h2.1.trans (h1.1.trans h0.1)

theorem prefix_input_ready (ops : Ops α) (input : Nat → Nat → α)
    (t row tid : Nat) (s : State α) (ready : InputReady input row tid s) :
    InputReady input row tid (prefixState ops input t s) := by
  unfold InputReady at *
  simpa only [prefix_memory] using ready

#print axioms component_index_frame
#print axioms components_other
#print axioms components_index_frame
#print axioms round_other
#print axioms round_index_frame
#print axioms initialized_other
#print axioms prefix_other
#print axioms prefix_input_ready
end LarkNativeFlashInferRmsNorm
