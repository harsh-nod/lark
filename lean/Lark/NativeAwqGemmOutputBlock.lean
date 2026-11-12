import Lark.NativeAwqGemmOutputMemory

/-! Complete K-loop output values and the global-memory frame for other
blocks. Values retain source accumulation order and final half conversion. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputStored outputRound outputLoop outputLane tailLane tailFold
  blockTail nextTile tileMatrix tileEnd tileNext kLoopState wholeBlock

theorem k_loop_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n t q : Nat) (s : State α) (positive : 0<n) (count : tile+n=p.k/32)
    (ht : t∈blockThreads (geometry p) b) (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    (kLoopState p ops input b tile n s).memory (outCell p t q)=
      some (ops.toHalf (kAccum p ops input b (p.k/32) (q/4) t (q%4))) := by
  induction n generalizing tile s with
  | zero => omega
  | succ n ih =>
    rw [kLoopState]
    by_cases last : n=0
    · subst n
      rw [if_pos rfl]
      unfold tileEnd
      have value := block_tail_value p ops tile b t q (tileValues p ops input tile b (kAccum p ops input b tile))
        (tileMatrix p ops input tile b (kAccum p ops input b tile) s) (by omega) ht hq guard
      simpa only [tileValues,show p.k/32=tile+1 by omega,kAccum] using value
    · rw [if_neg last]
      exact ih (tile+1) _ (by omega) (by omega)

theorem whole_block_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t q : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b) (hq : q<4*banks p)
    (guard : globalOutputRow p t (q%4)<p.m) :
    (wholeBlock p ops input b s).memory (outCell p t q)=
      some (ops.toHalf (kAccum p ops input b (p.k/32) (q/4) t (q%4))) := by
  unfold wholeBlock
  exact k_loop_output_value p ops input b 0 (p.k/32) t q _ (by have h := k_minimum p; omega)
    (by omega) ht hq guard

theorem after_middle_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (loc : Location) (space : loc.space=.global) :
    (afterMiddleBarrier p ops input tile b s).memory loc=s.memory loc := by
  apply after_middle_memory_outside p ops input tile b s loc
  · intro t _ e _ same
    have impossible := congrArg Location.space same
    simp only [space,aCell,sharedCell] at impossible
    cases impossible
  · intro t _ chunk _ e _ same
    have impossible := congrArg Location.space same
    simp only [space,bCell,sharedCell] at impossible
    cases impossible

theorem tile_matrix_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (loc : Location) (space : loc.space=.global) :
    (tileMatrix p ops input tile b acc s).memory loc=s.memory loc := by
  unfold tileMatrix
  rw [(matrix_phase_frames p ops input tile b acc _).1]
  exact after_middle_global_memory p ops input tile b s loc space

theorem tile_end_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (loc : Location) (space : loc.space=.global)
    (outside : ∀ t∈blockThreads (geometry p) b, ∀ q, q<4*banks p → loc≠outCell p t q) :
    (tileEnd p ops input tile b acc s).memory loc=s.memory loc := by
  unfold tileEnd blockTail
  exact (tail_fold_other_memory p ops tile _ _ _ loc outside).trans
    (tile_matrix_global_memory p ops input tile b acc s loc space)

theorem tile_next_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (loc : Location) (space : loc.space=.global)
    (outside : ∀ t∈blockThreads (geometry p) b, ∀ q, q<4*banks p → loc≠outCell p t q) :
    (tileNext p ops input tile b acc s).memory loc=s.memory loc := by
  unfold tileNext nextTile
  simpa only [tileEnd] using tile_end_global_memory p ops input tile b acc s loc space outside

theorem k_loop_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n : Nat) (s : State α) (loc : Location) (space : loc.space=.global)
    (outside : ∀ t∈blockThreads (geometry p) b, ∀ q, q<4*banks p → loc≠outCell p t q) :
    (kLoopState p ops input b tile n s).memory loc=s.memory loc := by
  induction n generalizing tile s with
  | zero => simp only [kLoopState]
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_global_memory p ops input tile b _ s loc space outside
    · exact (ih (tile+1) _).trans (tile_next_global_memory p ops input tile b _ s loc space outside)

theorem whole_block_global_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b : Nat) (s : State α) (loc : Location) (space : loc.space=.global)
    (outside : ∀ t∈blockThreads (geometry p) b, ∀ q, q<4*banks p → loc≠outCell p t q) :
    (wholeBlock p ops input b s).memory loc=s.memory loc := by
  unfold wholeBlock
  rw [k_loop_global_memory p ops input b 0 (p.k/32) _ loc space outside]
  exact congrFun (block_prefix_frames p ops b s).1 loc

theorem whole_block_other_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t q : Nat) (s : State α) (ht : t∉blockThreads (geometry p) b) (hq : q<4*banks p) :
    (wholeBlock p ops input b s).memory (outCell p t q)=s.memory (outCell p t q) :=
  whole_block_global_memory p ops input b s (outCell p t q) rfl
    (fun u hu j hj => out_cell_different_threads p t u q j hq hj (by intro same; subst u; exact ht hu))

#print axioms k_loop_output_value
#print axioms whole_block_output_value
#print axioms after_middle_global_memory
#print axioms tile_matrix_global_memory
#print axioms tile_end_global_memory
#print axioms tile_next_global_memory
#print axioms k_loop_global_memory
#print axioms whole_block_global_memory
#print axioms whole_block_other_output
end LarkNativeAwqGemm
