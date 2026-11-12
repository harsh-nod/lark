import Lark.NativeAwqGemmTailTrace

/-! Actual K32 trace classification and block-epoch parity across the two
source barriers. Other blocks retain their exact epochs throughout. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] matrixPhaseState blockTail nextTile tileMatrix tileEnd tileNext

theorem tile_matrix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (odd : BlockParity p b 1 s) : GoodTrace p (tileMatrix p ops input tile b acc s) := by
  unfold tileMatrix
  exact matrix_phase_good p ops input tile b acc _ (after_middle_good p ops input tile b s good odd)
    (after_middle_even p ops input tile b s odd)

theorem tile_end_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (odd : BlockParity p b 1 s) : GoodTrace p (tileEnd p ops input tile b acc s) := by
  unfold tileEnd
  exact block_tail_good p ops tile b _ _ (tile_matrix_good p ops input tile b acc s good odd)

theorem tile_end_even (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (odd : BlockParity p b 1 s) :
    BlockParity p b 0 (tileEnd p ops input tile b acc s) := by
  intro t ht
  unfold tileEnd
  rw [(block_tail_frames p ops tile b _ _).2]
  unfold tileMatrix
  rw [(matrix_phase_frames p ops input tile b acc _).2.2]
  exact after_middle_even p ops input tile b s odd t ht

theorem tile_end_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (tileEnd p ops input tile b acc s).epochs t=s.epochs t := by
  unfold tileEnd
  rw [(block_tail_frames p ops tile b _ _).2]
  unfold tileMatrix
  rw [(matrix_phase_frames p ops input tile b acc _).2.2]
  exact after_middle_epoch_other p ops input tile b t s ht

theorem tile_next_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (odd : BlockParity p b 1 s) : GoodTrace p (tileNext p ops input tile b acc s) := by
  unfold tileNext nextTile
  simpa only [tileEnd] using tile_end_good p ops input tile b acc s good odd

theorem tile_next_odd (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (odd : BlockParity p b 1 s) :
    BlockParity p b 1 (tileNext p ops input tile b acc s) := by
  intro t ht
  unfold tileNext nextTile
  rw [resume_epoch_block p b t _ ht]
  have even := tile_end_even p ops input tile b acc s odd t ht
  unfold tileEnd at even
  omega

theorem tile_next_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (tileNext p ops input tile b acc s).epochs t=s.epochs t := by
  unfold tileNext nextTile
  rw [resume_epoch_other p b t _ ht]
  simpa only [tileEnd] using tile_end_epoch_other p ops input tile b t acc s ht

#print axioms tile_matrix_good
#print axioms tile_end_good
#print axioms tile_end_even
#print axioms tile_end_epoch_other
#print axioms tile_next_good
#print axioms tile_next_odd
#print axioms tile_next_epoch_other
end LarkNativeAwqGemm
