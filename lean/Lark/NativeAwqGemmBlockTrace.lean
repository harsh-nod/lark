import Lark.NativeAwqGemmTileTrace

/-! Complete K-loop trace classification from the actual first barrier.
Every complete block ends at an even epoch and preserves other blocks. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] tileEnd tileNext kLoopState wholeBlock

theorem k_loop_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n : Nat) (s : State α) (good : GoodTrace p s) (odd : BlockParity p b 1 s) :
    GoodTrace p (kLoopState p ops input b tile n s) := by
  induction n generalizing tile s with
  | zero => simpa only [kLoopState] using good
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_good p ops input tile b _ s good odd
    · exact ih (tile+1) _ (tile_next_good p ops input tile b _ s good odd) (tile_next_odd p ops input tile b _ s odd)

theorem k_loop_even (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n : Nat) (s : State α) (positive : 0<n) (odd : BlockParity p b 1 s) :
    BlockParity p b 0 (kLoopState p ops input b tile n s) := by
  induction n generalizing tile s with
  | zero => omega
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_even p ops input tile b _ s odd
    · rename_i remaining
      exact ih (tile+1) _ (by omega) (tile_next_odd p ops input tile b _ s odd)

theorem k_loop_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (kLoopState p ops input b tile n s).epochs t=s.epochs t := by
  induction n generalizing tile s with
  | zero => simp only [kLoopState]
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_epoch_other p ops input tile b t _ s ht
    · exact (ih (tile+1) _).trans (tile_next_epoch_other p ops input tile b t _ s ht)

theorem after_first_good (p : Shape) (ops : Ops α) (b : Nat) (s : State α) (good : GoodTrace p s) :
    GoodTrace p (afterFirstBarrier p ops b s) :=
  good_trace_of_trace p s _ good (block_prefix_frames p ops b s).2.1

theorem after_first_odd (p : Shape) (ops : Ops α) (b : Nat) (s : State α) (even : BlockParity p b 0 s) :
    BlockParity p b 1 (afterFirstBarrier p ops b s) := by
  intro t ht
  unfold afterFirstBarrier
  rw [resume_epoch_block p b t _ ht,(block_prefix_frames p ops b s).2.2]
  have h := even t ht
  omega

theorem after_first_epoch_other (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∉blockThreads (geometry p) b) : (afterFirstBarrier p ops b s).epochs t=s.epochs t := by
  unfold afterFirstBarrier
  rw [resume_epoch_other p b t _ ht,(block_prefix_frames p ops b s).2.2]

theorem whole_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (good : GoodTrace p s) (even : BlockParity p b 0 s) : GoodTrace p (wholeBlock p ops input b s) := by
  unfold wholeBlock
  exact k_loop_good p ops input b 0 (p.k/32) _ (after_first_good p ops b s good) (after_first_odd p ops b s even)

theorem whole_block_epoch_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t∉blockThreads (geometry p) b) :
    (wholeBlock p ops input b s).epochs t=s.epochs t := by
  unfold wholeBlock
  rw [k_loop_epoch_other p ops input b 0 (p.k/32) t _ ht]
  exact after_first_epoch_other p ops b t s ht

theorem whole_block_even (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α)
    (even : ∀ t, (s.epochs t).block%2=0) : ∀ t, ((wholeBlock p ops input b s).epochs t).block%2=0 := by
  intro t
  by_cases ht : t∈blockThreads (geometry p) b
  · unfold wholeBlock
    exact k_loop_even p ops input b 0 (p.k/32) _ (by have h := k_minimum p; omega)
      (after_first_odd p ops b s (fun u _ => even u)) t ht
  · rw [whole_block_epoch_other p ops input b t s ht]
    exact even t

#print axioms k_loop_good
#print axioms k_loop_even
#print axioms k_loop_epoch_other
#print axioms after_first_good
#print axioms after_first_odd
#print axioms after_first_epoch_other
#print axioms whole_block_good
#print axioms whole_block_epoch_other
#print axioms whole_block_even
end LarkNativeAwqGemm
