import Lark.InOut

/-! Opt-in scalar-machine correctness for explicitly initialized mutable
buffers. The original execution, bounds, race test and extraction are unchanged. -/
namespace LarkInOutScalar
open LarkNonlinear

def Correct (ops : Ops α) (layout : Layout) (mutable : List Nat) (g : Geometry) (f : Fuel)
    (program : List Instr) (spec : (Nat → Nat → α) → List α) : Prop :=
  LarkInOut.Valid layout mutable ∧ ∀ input outside, ∃ final,
    runLaunch ops layout g f program (LarkInOut.initial layout mutable input outside) = some final ∧
    raceFree g final.trace = true ∧ extract layout final = some (spec input)

theorem correct_from_pre (ops : Ops α) (layout : Layout) (mutable : List Nat) (g : Geometry) (f : Fuel)
    (program : List Instr) (spec : (Nat → Nat → α) → List α)
    (correct : Correct ops layout mutable g f program spec) (input : Nat → Nat → α) (s : State α)
    (pre : LarkInOut.StdPre layout mutable input s) :
    ∃ final, runLaunch ops layout g f program s = some final ∧
      raceFree g final.trace = true ∧ extract layout final = some (spec input) := by
  obtain ⟨outside, rfl⟩ := pre
  exact correct.2 input outside

#print axioms correct_from_pre
end LarkInOutScalar

-- changed pinned model
