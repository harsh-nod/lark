import Lark.NativeAwqGemmKLoop

/-! Complete block execution preserves other blocks' program counters and
the read-only input buffers, allowing the original grid scheduler to compose. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands
  matrixState matrixBankState matrixFold matrixPassState matrixPhaseState stagingFold stagingState
  outputRound outputStored outputLoop outputLane tailLane tailFold blockTail nextTile tileMatrix tileEnd tileNext kLoopState

theorem matrix_bank_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank u : Nat) (acc : Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (matrixBankState p ops input tile b half bank acc s).pc u=s.pc u := by
  unfold matrixBankState
  rw [matrix_state_pc,if_neg hu]
  unfold blockOperands
  exact (operand_fold_other p ops input tile half bank u _ s hu).1

theorem matrix_fold_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n u : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (matrixFold p ops input tile b half acc bank n s).pc u=s.pc u := by
  induction n generalizing bank s with
  | zero => simp only [matrixFold]
  | succ n ih =>
    rw [matrixFold]
    exact (ih (bank+1) (matrixBankState p ops input tile b half bank (acc bank) s)).trans
      (matrix_bank_other_pc p ops input tile b half bank u (acc bank) s hu)

theorem matrix_phase_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b u : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (matrixPhaseState p ops input tile b acc s).pc u=s.pc u := by
  unfold matrixPhaseState matrixPassState
  exact (matrix_fold_other_pc p ops input tile b 1 0 (banks p) u _ _ hu).trans
    (matrix_fold_other_pc p ops input tile b 0 0 (banks p) u acc s hu)

theorem resume_other_pc (p : Shape) (b u : Nat) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (resume (blockThreads (geometry p) b) .block s).pc u=s.pc u := by
  have outside : ¬(blockThreads (geometry p) b).contains u=true := by
    simpa only [List.contains_iff_mem] using hu
  simp only [resume,if_neg outside]

theorem after_middle_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b u : Nat) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (afterMiddleBarrier p ops input tile b s).pc u=s.pc u := by
  unfold afterMiddleBarrier
  rw [resume_other_pc p b u _ hu]
  exact (staging_fold_other p ops input tile u _ s hu).1

theorem tile_matrix_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b u : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (tileMatrix p ops input tile b acc s).pc u=s.pc u := by
  unfold tileMatrix
  exact (matrix_phase_other_pc p ops input tile b u acc _ hu).trans (after_middle_other_pc p ops input tile b u s hu)

theorem tile_end_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b u : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (tileEnd p ops input tile b acc s).pc u=s.pc u := by
  unfold tileEnd blockTail
  exact (tail_fold_other p ops tile u _ _ _ hu).1.trans (tile_matrix_other_pc p ops input tile b u acc s hu)

theorem tile_next_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b u : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (tileNext p ops input tile b acc s).pc u=s.pc u := by
  unfold tileNext nextTile
  rw [resume_other_pc p b u _ hu]
  simpa only [tileEnd] using tile_end_other_pc p ops input tile b u acc s hu

theorem tile_end_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (tileEnd p ops input tile b acc s) := by
  unfold tileEnd
  apply block_tail_reads p ops input tile b _ _
  unfold Reads tileMatrix
  rw [(matrix_phase_frames p ops input tile b acc _).1]
  exact after_middle_reads p ops input tile b s reads

theorem k_loop_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n u : Nat) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (kLoopState p ops input b tile n s).pc u=s.pc u := by
  induction n generalizing tile s with
  | zero => simp only [kLoopState]
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_other_pc p ops input tile b u _ s hu
    · exact (ih (tile+1) _).trans (tile_next_other_pc p ops input tile b u _ s hu)

theorem k_loop_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (kLoopState p ops input b tile n s) := by
  induction n generalizing tile s with
  | zero => simpa only [kLoopState] using reads
  | succ n ih =>
    rw [kLoopState]
    split
    · exact tile_end_reads p ops input tile b _ s reads
    · exact ih (tile+1) _ (tile_next_reads p ops input tile b _ s reads)

theorem whole_block_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b u : Nat) (s : State α) (hu : u∉blockThreads (geometry p) b) :
    (wholeBlock p ops input b s).pc u=s.pc u := by
  unfold wholeBlock
  rw [k_loop_other_pc p ops input b 0 (p.k/32) u _ hu]
  unfold afterFirstBarrier
  rw [resume_other_pc p b u _ hu]
  exact (prefix_fold_other p ops _ u s hu).1

theorem whole_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b : Nat) (s : State α) (reads : Reads p input s) : Reads p input (wholeBlock p ops input b s) :=
  k_loop_reads p ops input b 0 (p.k/32) _ (after_first_reads p ops b s input reads)

#print axioms matrix_bank_other_pc
#print axioms matrix_fold_other_pc
#print axioms matrix_phase_other_pc
#print axioms resume_other_pc
#print axioms after_middle_other_pc
#print axioms tile_matrix_other_pc
#print axioms tile_end_other_pc
#print axioms tile_next_other_pc
#print axioms tile_end_reads
#print axioms k_loop_other_pc
#print axioms k_loop_reads
#print axioms whole_block_other_pc
#print axioms whole_block_reads
end LarkNativeAwqGemm
