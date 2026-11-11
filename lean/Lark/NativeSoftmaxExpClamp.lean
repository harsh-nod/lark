import Lark.NativeSoftmaxExpStart

/-! The actual conditional clamped-index path in the exponentiation input-buffer pass. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expClampedState (t col : Nat) (s : State α) : State α :=
  if 50257 ≤ col then setIndex (advance s t 51) t 11 50256 52 else advance s t 52

theorem exp_clamp_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t col extra : Nat) (s : State α)
    (hp : s.pc t = 50) (h11 : s.indices t 11 = some (col : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + clampCost col) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expClampedState t col s) := by
  by_cases hc : 50257 ≤ col
  · have hci : (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 11)) = some true := by
      simp [evalPredicate,evalIndex,h11,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 11)) 52) s = some (advance s t 51) := by
      simp [execute,pred,hp]
    have e2 := execute_index_of ops (layout p) (geometry p) t 11 52 (.const 50256)
      (advance s t 51) 50256 rfl (by simp [advance])
    simp only [clampCost,if_pos hc]
    rewrite [show extra + 2 = (extra + 1) + 1 by omega,
      scalar_step p guarded ops t 50 _ _ s _ (by cases guarded <;> decide) hp e1]
    rewrite [scalar_step p guarded ops t 51 _ _ _ _ (by cases guarded <;> decide)
      (by simp [advance]) e2]
    simp only [expClampedState,if_pos hc]
  · have hci : ¬ (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 11)) = some false := by
      simp [evalPredicate,evalIndex,h11,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 11)) 52) s = some (advance s t 52) := by
      simp [execute,pred,hp]
    simp only [clampCost,if_neg hc,expClampedState]
    rewrite [scalar_step p guarded ops t 50 _ _ s _ (by cases guarded <;> decide) hp e1]
    simp only [if_neg hc]

theorem exp_clamped_fields (t col : Nat) (s : State α)
    (h11 : s.indices t 11 = some (col : Int)) :
    (expClampedState t col s).pc t = 52 ∧
    (expClampedState t col s).indices t 11 = some ((clamped col : Nat) : Int) := by
  by_cases hc : 50257 ≤ col
  · have hm : clamped col = 50256 := by unfold clamped; omega
    simp [expClampedState,hc,setIndex,advance,hm]
  · have hm : clamped col = col := by unfold clamped; omega
    simp [expClampedState,hc,advance,h11,hm]

theorem exp_clamped_index_other (t col r : Nat) (s : State α) (hr : r ≠ 11) :
    (expClampedState t col s).indices t r = s.indices t r := by
  unfold expClampedState
  split <;> simp [setIndex,advance,hr]

theorem exp_clamped_preserves (t col : Nat) (s : State α) :
    (expClampedState t col s).memory = s.memory ∧
    (expClampedState t col s).trace = s.trace ∧
    (expClampedState t col s).epochs = s.epochs ∧
    (expClampedState t col s).regs = s.regs := by
  unfold expClampedState
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms exp_clamp_eq
#print axioms exp_clamped_fields
#print axioms exp_clamped_index_other
#print axioms exp_clamped_preserves
end LarkNativeSoftmax
