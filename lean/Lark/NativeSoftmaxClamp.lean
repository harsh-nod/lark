import Lark.NativeSoftmaxInit

/-! The actual conditional clamped-index path in the first source pass. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def clampCost (col : Nat) : Nat := if 50257 ≤ col then 2 else 1

def clampedState (t col : Nat) (s : State α) : State α :=
  if 50257 ≤ col then setIndex (advance s t 11) t 6 50256 12 else advance s t 12

theorem clamp_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t col extra : Nat) (s : State α)
    (hp : s.pc t = 10) (h6 : s.indices t 6 = some (col : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + clampCost col) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (clampedState t col s) := by
  by_cases hc : 50257 ≤ col
  · have hci : (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 6)) = some true := by
      simp [evalPredicate,evalIndex,h6,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 6)) 12) s = some (advance s t 11) := by
      simp [execute,pred,hp]
    have e2 := execute_index_of ops (layout p) (geometry p) t 6 12 (.const 50256)
      (advance s t 11) 50256 rfl (by simp [advance])
    simp only [clampCost,if_pos hc]
    rewrite [show extra + 2 = (extra + 1) + 1 by omega,
      scalar_step p guarded ops t 10 _ _ s _ (by cases guarded <;> decide) hp e1]
    rewrite [scalar_step p guarded ops t 11 _ _ _ _ (by cases guarded <;> decide)
      (by simp [advance]) e2]
    simp only [clampedState,if_pos hc]
  · have hci : ¬ (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 6)) = some false := by
      simp [evalPredicate,evalIndex,h6,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 6)) 12) s = some (advance s t 12) := by
      simp [execute,pred,hp]
    simp only [clampCost,if_neg hc,clampedState]
    rewrite [scalar_step p guarded ops t 10 _ _ s _ (by cases guarded <;> decide) hp e1]
    simp only [if_neg hc]

theorem clamped_fields (t col : Nat) (s : State α)
    (h6 : s.indices t 6 = some (col : Int)) :
    (clampedState t col s).pc t = 12 ∧
    (clampedState t col s).indices t 6 = some ((clamped col : Nat) : Int) := by
  by_cases hc : 50257 ≤ col
  · have hm : clamped col = 50256 := by unfold clamped; omega
    simp [clampedState,hc,setIndex,advance,hm]
  · have hm : clamped col = col := by unfold clamped; omega
    simp [clampedState,hc,advance,h6,hm]

theorem clamped_index_other (t col r : Nat) (s : State α) (hr : r ≠ 6) :
    (clampedState t col s).indices t r = s.indices t r := by
  unfold clampedState
  split <;> simp [setIndex,advance,hr]

theorem clamped_preserves (t col : Nat) (s : State α) :
    (clampedState t col s).memory = s.memory ∧
    (clampedState t col s).trace = s.trace ∧
    (clampedState t col s).epochs = s.epochs ∧
    (clampedState t col s).regs = s.regs := by
  unfold clampedState
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms clamp_eq
#print axioms clamped_fields
#print axioms clamped_index_other
#print axioms clamped_preserves
end LarkNativeSoftmax
