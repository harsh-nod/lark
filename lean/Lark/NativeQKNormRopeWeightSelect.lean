import Lark.NativeQKNormRopeWeightLoad

/-! The actual head-dependent Q/K branch, weight reads, and Q-only jump. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def weightBuffer (t : Nat) : Nat := if head t < 32 then 2 else 3
def weightStart (t : Nat) : Nat := if head t < 32 then 42 else 47
def weightSteps (t : Nat) : Nat := if head t < 32 then 6 else 5

def weightSelected (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let after := weightFourLoads ops input t (weightBuffer t) (weightStart t) (advance s t (weightStart t))
  if head t < 32 then advance after t 51 else after

theorem weight_branch_eq (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat)
    (s : State α) (hp : s.pc t = 41) (hh : s.indices t 2 = some ((head t : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (advance s t (weightStart t)) := by
  have ex : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 2) (.const 32)) 47) s =
      some (advance s t (weightStart t)) := by
    by_cases h : head t < 32
    · have pred := predicate_lt_of (geometry p) t s (.ivar 2) (.const 32) (head t : Int) 32 hh rfl (by omega)
      simp [execute, pred, hp, weightStart, h]
    · have pred := predicate_nlt_of (geometry p) t s (.ivar 2) (.const 32) (head t : Int) 32 hh rfl (by omega)
      simp [execute, pred, weightStart, h]
  exact scalar_step p neox ops t 41 extra _ s _ (by cases neox <;> decide) hp ex

theorem weight_selected_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (hp : s.pc t = 41)
    (hh : s.indices t 2 = some ((head t : Nat) : Int))
    (hi : ∀ e, e < 4 → s.indices t (11 + e) = some ((column t e : Nat) : Int))
    (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + weightSteps t) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (weightSelected ops input t s) := by
  by_cases h : head t < 32
  · simp only [weightSteps, h, if_true]
    rewrite [weight_branch_eq p neox ops t (extra + 5) s hp hh]
    simp only [weightStart, h, if_true]
    rewrite [weight_four_eq p neox ops input t 2 42 (extra + 1) (advance s t 42)
      (Or.inl ⟨rfl, rfl⟩) (by simp [advance]) hi hr]
    have pc := weight_four_pc ops input t 2 42 (advance s t 42)
    rewrite [scalar_step p neox ops t 46 extra (.jump 51) _ _ (by cases neox <;> decide) pc rfl]
    simp only [weightSelected, weightBuffer, weightStart, h, if_true]
  · simp only [weightSteps, h, if_false]
    rewrite [weight_branch_eq p neox ops t (extra + 4) s hp hh]
    simp only [weightStart, h, if_false]
    rewrite [weight_four_eq p neox ops input t 3 47 extra (advance s t 47)
      (Or.inr ⟨rfl, rfl⟩) (by simp [advance]) hi hr]
    simp only [weightSelected, weightBuffer, weightStart, h, if_false]

theorem weight_selected_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (weightSelected ops input t s).pc t = 51 := by
  by_cases h : head t < 32
  · simp [weightSelected, h, advance]
  · simp only [weightSelected, weightStart, h, if_neg]
    exact weight_four_pc ops input t (weightBuffer t) 47 (advance s t 47)

theorem weight_selected_value (ops : Ops α) (input : Nat → Nat → α) (t e : Nat)
    (s : State α) (he : e < 4) :
    (weightSelected ops input t s).regs t (13 + e) = some (weightValue ops input t (weightBuffer t) e) := by
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · exact weight_four_value ops input t (weightBuffer t) (weightStart t) e _ he
  · exact weight_four_value ops input t (weightBuffer t) (weightStart t) e _ he

theorem weight_selected_low (ops : Ops α) (input : Nat → Nat → α) (t r : Nat)
    (s : State α) (hr : r < 13) : (weightSelected ops input t s).regs t r = s.regs t r := by
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · exact weight_four_low ops input t (weightBuffer t) (weightStart t) r _ hr
  · exact weight_four_low ops input t (weightBuffer t) (weightStart t) r _ hr

theorem weight_selected_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (weightSelected ops input t s).memory = s.memory ∧
    (weightSelected ops input t s).indices = s.indices ∧
    (weightSelected ops input t s).epochs = s.epochs := by
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · exact weight_four_preserves ops input t (weightBuffer t) (weightStart t) _
  · exact weight_four_preserves ops input t (weightBuffer t) (weightStart t) _

theorem weight_selected_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (weightSelected ops input t s).trace =
      [⟨t, globalCell (weightBuffer t) (column t 3), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 2), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 1), false, s.epochs t⟩,
       ⟨t, globalCell (weightBuffer t) (column t 0), false, s.epochs t⟩] ++ s.trace := by
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · exact weight_four_trace ops input t (weightBuffer t) (weightStart t) _
  · exact weight_four_trace ops input t (weightBuffer t) (weightStart t) _

theorem weight_selected_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (weightSelected ops input t s).trace, Good a := by
  have hb : 1 ≤ weightBuffer t ∧ weightBuffer t ≤ 4 := by unfold weightBuffer; split <;> omega
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · exact weight_four_good ops input t (weightBuffer t) (weightStart t) _ hb good
  · exact weight_four_good ops input t (weightBuffer t) (weightStart t) _ hb good

theorem weight_selected_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat)
    (s : State α) (hu : u ≠ t) :
    (weightSelected ops input t s).pc u = s.pc u ∧ (weightSelected ops input t s).regs u = s.regs u := by
  by_cases h : head t < 32 <;> simp only [weightSelected, h, if_pos, if_neg]
  · have hf := weight_four_other ops input t (weightBuffer t) (weightStart t) u (advance s t (weightStart t)) hu
    simpa [advance, hu] using hf
  · have hf := weight_four_other ops input t (weightBuffer t) (weightStart t) u (advance s t (weightStart t)) hu
    simpa [advance, hu] using hf

#print axioms weight_branch_eq
#print axioms weight_selected_eq
#print axioms weight_selected_pc
#print axioms weight_selected_value
#print axioms weight_selected_low
#print axioms weight_selected_preserves
#print axioms weight_selected_trace
#print axioms weight_selected_good
#print axioms weight_selected_other
end LarkNativeQKNormRope
