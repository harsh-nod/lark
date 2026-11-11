import Lark.InOut
import Lark.PartitionCollective

/-! Whole-launch correctness for explicit initialized mutable buffers under the
partition-aware collective machine. The initializer is seeded and both output
buffers are extracted by the original machine. No uninitialized-output contract
is substituted for an in-place source.
-/
namespace LarkInOutPartition
open LarkNonlinear

def Correct (ops : Ops α) (layout : Layout) (mutable : List Nat) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (spec : (Nat → Nat → α) → List α) : Prop :=
  LarkInOut.Valid layout mutable ∧ ∀ input outside, ∃ final,
    LarkPartitionCollective.runLaunch ops layout g f p (LarkInOut.initial layout mutable input outside) = some final ∧
    raceFree g final.trace = true ∧ extract layout final = some (spec input)

theorem correct_from_pre (ops : Ops α) (layout : Layout) (mutable : List Nat) (g : Geometry) (f : Fuel)
    (p : List LarkCollective.Instr) (spec : (Nat → Nat → α) → List α)
    (h : Correct ops layout mutable g f p spec) (input : Nat → Nat → α) (s : State α)
    (pre : LarkInOut.StdPre layout mutable input s) :
    ∃ final, LarkPartitionCollective.runLaunch ops layout g f p s = some final ∧
      raceFree g final.trace = true ∧ extract layout final = some (spec input) := by
  obtain ⟨outside,rfl⟩ := pre
  exact h.2 input outside

#print axioms correct_from_pre
end LarkInOutPartition
