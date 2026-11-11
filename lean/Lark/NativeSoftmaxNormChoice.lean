import Lark.NativeSoftmaxNormCode

/-! The actual conditional clamped-index path in the original normalization buffer pass. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normOriginalClampedState (t col : Nat) (s : State α) : State α :=
  if 50257 ≤ col then setIndex (advance s t 100) t 19 50256 101 else advance s t 101

theorem norm_original_clamp_eq (p : Shape) (ops : Ops α) (t col extra : Nat) (s : State α)
    (hp : s.pc t = 99) (h19 : s.indices t 19 = some (col : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + clampCost col) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra
        (normOriginalClampedState t col s) := by
  by_cases hc : 50257 ≤ col
  · have hci : (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 19)) = some true := by
      simp [evalPredicate,evalIndex,h19,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 19)) 101) s = some (advance s t 100) := by
      simp [execute,pred,hp]
    have e2 := execute_index_of ops (layout p) (geometry p) t 19 101 (.const 50256)
      (advance s t 100) 50256 rfl (by simp [advance])
    simp only [clampCost,if_pos hc]
    rewrite [show extra + 2 = (extra + 1) + 1 by omega,
      scalar_step p false ops t 99 _ _ s _ (by decide) hp e1]
    rewrite [scalar_step p false ops t 100 _ _ _ _ (by decide)
      (by simp [advance]) e2]
    simp only [normOriginalClampedState,if_pos hc]
  · have hci : ¬ (50257 : Int) ≤ (col : Int) := by omega
    have pred : evalPredicate (geometry p) t s (.le (.const 50257) (.ivar 19)) = some false := by
      simp [evalPredicate,evalIndex,h19,int32,hci]
    have e1 : execute ops (layout p) (geometry p) t
        (.branch (.le (.const 50257) (.ivar 19)) 101) s = some (advance s t 101) := by
      simp [execute,pred,hp]
    simp only [clampCost,if_neg hc,normOriginalClampedState]
    rewrite [scalar_step p false ops t 99 _ _ s _ (by decide) hp e1]
    simp only [if_neg hc]

theorem norm_original_clamped_fields (t col : Nat) (s : State α)
    (h19 : s.indices t 19 = some (col : Int)) :
    (normOriginalClampedState t col s).pc t = 101 ∧
    (normOriginalClampedState t col s).indices t 19 = some ((clamped col : Nat) : Int) := by
  by_cases hc : 50257 ≤ col
  · have hm : clamped col = 50256 := by unfold clamped; omega
    simp [normOriginalClampedState,hc,setIndex,advance,hm]
  · have hm : clamped col = col := by unfold clamped; omega
    simp [normOriginalClampedState,hc,advance,h19,hm]

theorem norm_original_clamped_index_other (t col r : Nat) (s : State α) (hr : r ≠ 19) :
    (normOriginalClampedState t col s).indices t r = s.indices t r := by
  unfold normOriginalClampedState
  split <;> simp [setIndex,advance,hr]

theorem norm_original_clamped_preserves (t col : Nat) (s : State α) :
    (normOriginalClampedState t col s).memory = s.memory ∧
    (normOriginalClampedState t col s).trace = s.trace ∧
    (normOriginalClampedState t col s).epochs = s.epochs ∧
    (normOriginalClampedState t col s).regs = s.regs := by
  unfold normOriginalClampedState
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

def normChoice (guarded : Bool) (t col : Nat) (s : State α) : State α :=
  if guarded then advance s t (if col<50257 then 100 else 102) else normOriginalClampedState t col s

def normChoiceCost (guarded : Bool) (col : Nat) : Nat := if guarded then 1 else clampCost col

def normChoicePc (guarded : Bool) (col : Nat) : Nat := if guarded then (if col<50257 then 100 else 102) else 101

def normSelectedColumn (guarded : Bool) (col : Nat) : Nat := if guarded then col else clamped col

theorem norm_choice_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t col extra : Nat) (s : State α)
    (hp : s.pc t=99) (hi : s.indices t 19=some (col : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+normChoiceCost guarded col) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normChoice guarded t col s) := by
  cases guarded with
  | false => exact norm_original_clamp_eq p ops t col extra s hp hi
  | true =>
    by_cases hc : col<50257
    · have hci : (col : Int)<50257 := by omega
      have pred : evalPredicate (geometry p) t s (.lt (.ivar 19) (.const 50257))=some true := by
        simp [evalPredicate,evalIndex,hi,int32,hci]
      have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 19) (.const 50257)) 102) s=
          some (advance s t 100) := by simp [execute,pred,hp]
      simpa only [normChoiceCost,normChoice,Bool.true_eq,↓reduceIte,if_pos hc] using
        scalar_step p true ops t 99 extra _ s _ (by decide) hp e
    · have hci : ¬ (col : Int)<50257 := by omega
      have pred : evalPredicate (geometry p) t s (.lt (.ivar 19) (.const 50257))=some false := by
        simp [evalPredicate,evalIndex,hi,int32,hci]
      have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 19) (.const 50257)) 102) s=
          some (advance s t 102) := by simp [execute,pred]
      simpa only [normChoiceCost,normChoice,Bool.true_eq,↓reduceIte,if_neg hc] using
        scalar_step p true ops t 99 extra _ s _ (by decide) hp e

theorem norm_choice_fields (guarded : Bool) (t col : Nat) (s : State α) (hi : s.indices t 19=some (col : Int)) :
    (normChoice guarded t col s).pc t=normChoicePc guarded col ∧
    (normChoice guarded t col s).indices t 19=some ((normSelectedColumn guarded col : Nat) : Int) := by
  cases guarded with
  | false => exact norm_original_clamped_fields t col s hi
  | true => simp [normChoice,normChoicePc,normSelectedColumn,advance,hi]

theorem norm_choice_index_other (guarded : Bool) (t col r : Nat) (s : State α) (hr : r ≠ 19) :
    (normChoice guarded t col s).indices t r=s.indices t r := by
  cases guarded with
  | false => exact norm_original_clamped_index_other t col r s hr
  | true => rfl

theorem norm_choice_frames (guarded : Bool) (t col : Nat) (s : State α) :
    (normChoice guarded t col s).memory=s.memory ∧ (normChoice guarded t col s).trace=s.trace ∧
    (normChoice guarded t col s).epochs=s.epochs ∧ (normChoice guarded t col s).regs=s.regs := by
  cases guarded with
  | false => exact norm_original_clamped_preserves t col s
  | true => exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms norm_original_clamp_eq
#print axioms norm_original_clamped_fields
#print axioms norm_original_clamped_index_other
#print axioms norm_original_clamped_preserves
#print axioms norm_choice_eq
#print axioms norm_choice_fields
#print axioms norm_choice_index_other
#print axioms norm_choice_frames
end LarkNativeSoftmax
