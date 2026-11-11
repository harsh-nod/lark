import Lark.NativeSoftmaxMaxPrefix

/-! The actual maximum-prefix trace consists exclusively of input reads. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def MaxInputAccess (a : Access) : Prop :=
  a.location.space = .global ∧ a.location.owner = 0 ∧
    a.location.buffer = 1 ∧ a.write = false

theorem max_component_inputs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxComponentAfter ops input row tid iteration component t acc s).trace,
      MaxInputAccess a := by
  intro a ha
  rewrite [(max_component_fields ops input row tid iteration component t acc s).2.2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · exact old a ha

theorem max_components_inputs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α)
    (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxComponents ops input row tid iteration t component count acc s).trace,
      MaxInputAccess a := by
  induction count generalizing component acc s with
  | zero => exact old
  | succ count ih =>
    exact ih (component+1) _ _ (max_component_inputs ops input row tid iteration component t acc s old)

theorem max_round_inputs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxRoundAfter ops input row tid iteration t acc s).trace, MaxInputAccess a :=
  max_components_inputs ops input row tid iteration t 0 8 acc (maxBeginRound t s) old

theorem max_rounds_inputs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count : Nat) (acc : α) (s : State α)
    (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxRounds ops input row tid t iteration count acc s).trace, MaxInputAccess a := by
  induction count generalizing iteration acc s with
  | zero => exact old
  | succ count ih =>
    exact ih (iteration+1) _ _ (max_round_inputs ops input row tid iteration t acc s old)

theorem max_prefix_inputs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (old : ∀ a ∈ s.trace, MaxInputAccess a) :
    ∀ a ∈ (maxPrefixState ops input t s).trace, MaxInputAccess a := by
  unfold maxPrefixState
  rewrite [(max_exit_preserves ops t (maxPassState ops input t s)).2.2.1]
  exact max_rounds_inputs ops input (t/1024) (t%1024) t 0 7 _ (initialized ops t s) old

theorem initial_max_prefix_inputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (maxPrefixState ops input t (initial (layout p) input outside)).trace, MaxInputAccess a :=
  max_prefix_inputs ops input t _ (by intro a ha; cases ha)

#print axioms max_component_inputs
#print axioms max_components_inputs
#print axioms max_round_inputs
#print axioms max_rounds_inputs
#print axioms max_prefix_inputs
#print axioms initial_max_prefix_inputs
end LarkNativeSoftmax
