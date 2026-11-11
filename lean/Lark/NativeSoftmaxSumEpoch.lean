import Lark.NativeSoftmaxWholeBlock

/-! Full per-thread epochs after the four actual reduction block phases.
All scalar/native-shuffle phases preserve epochs, and each actual block resume
increments only the block component. This also fixes the common grid epoch of
the original conflicting accesses, without assuming intermediate states. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mid_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (midState p ops input row s).epochs (row*1024+tid)=bumpEpoch (s.epochs (row*1024+tid)) .block := by
  simp only [midState,resume,block_contains p row tid ht,↓reduceIte,first_block_epochs]

theorem after_maximum_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (afterMaximum p ops input row s).epochs (row*1024+tid)=bumpEpoch (s.epochs (row*1024+tid)) .block := by
  simp only [afterMaximum,resume,block_contains p row tid ht,↓reduceIte,serial_block_epochs]

theorem after_exp_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (afterExp p ops input row s).epochs (row*1024+tid)=bumpEpoch (s.epochs (row*1024+tid)) .block := by
  simp only [afterExp,resume,block_contains p row tid ht,↓reduceIte,exp_block_epochs]

theorem after_sum_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (afterSum p ops input row s).epochs (row*1024+tid)=bumpEpoch (s.epochs (row*1024+tid)) .block := by
  simp only [afterSum,resume,block_contains p row tid ht,↓reduceIte,sum_serial_block_epochs]

theorem sum_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (sumState p ops input row s).epochs (row*1024+tid)=
      { s.epochs (row*1024+tid) with block := (s.epochs (row*1024+tid)).block+4 } := by
  simp only [sumState,maximumState,after_sum_full_epoch p ops input row tid _ ht,
    after_exp_full_epoch p ops input row tid _ ht,after_maximum_full_epoch p ops input row tid _ ht,
    mid_full_epoch p ops input row tid _ ht,bumpEpoch,Nat.add_assoc]

theorem initial_sum_full_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (ht : tid<1024) :
    (sumState p ops input row (initial (layout p) input outside)).epochs (row*1024+tid)=⟨0,4,0⟩ := by
  rewrite [sum_full_epoch p ops input row tid _ ht]
  rfl

#print axioms mid_full_epoch
#print axioms after_maximum_full_epoch
#print axioms after_exp_full_epoch
#print axioms after_sum_full_epoch
#print axioms sum_full_epoch
#print axioms initial_sum_full_epoch
end LarkNativeSoftmax
