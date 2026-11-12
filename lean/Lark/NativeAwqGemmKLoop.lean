import Lark.NativeAwqGemmTileStep

/-! Complete K32-loop induction using exactly the source's two block visits
per tile. The final visit includes every original guarded output pair. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands
  matrixState matrixBankState matrixFold matrixPassState matrixPhaseState stagingFold stagingState
  outputRound outputStored outputLoop outputLane tailLane tailFold blockTail nextTile tileMatrix tileEnd tileNext

def kAccum (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) : Nat → Nat → Nat → Nat → α
  | 0 => fun _ _ _ => ops.literal 0 1
  | tile+1 => matrixPhaseResult p ops input tile b (kAccum p ops input b tile)

def kLoopState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) : Nat → Nat → State α → State α
  | _,0,s => s
  | tile,n+1,s => if n=0 then tileEnd p ops input tile b (kAccum p ops input b tile) s
      else kLoopState p ops input b (tile+1) n (tileNext p ops input tile b (kAccum p ops input b tile) s)

theorem k_loop_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n : Nat) (s : State α) (positive : 0<n) (count : tile+n=p.k/32)
    (reads : Reads p input s) (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 →
      s.regs t (bank*4+e)=some (kAccum p ops input b tile bank t e)) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (2*n) s=
      some (kLoopState p ops input b tile n s) := by
  induction n generalizing tile s with
  | zero => omega
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,tile_run_step p ops input tile b (2*n)
      (kAccum p ops input b tile) s (by omega) reads starts hc]
    by_cases last : n=0
    · subst n
      rw [if_neg (show ¬tile+1<p.k/32 by omega),kLoopState,if_pos rfl]
    · rw [if_pos (show tile+1<p.k/32 by omega),kLoopState,if_neg last]
      exact ih (tile+1) (tileNext p ops input tile b (kAccum p ops input b tile) s) (by omega) (by omega)
        (tile_next_reads p ops input tile b _ s reads)
        (fun t ht => tile_next_start p ops input tile b t _ s (by omega) ht starts)
        (fun bank hb t ht e he => by
          simpa only [kAccum] using tile_next_accumulator p ops input tile b bank t e
            (kAccum p ops input b tile) s hb ht he)

theorem k_loop_halt (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n t : Nat) (s : State α) (positive : 0<n) (count : tile+n=p.k/32)
    (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    (kLoopState p ops input b tile n s).pc t=haltPC p := by
  induction n generalizing tile s with
  | zero => omega
  | succ n ih =>
    rw [kLoopState]
    by_cases last : n=0
    · subst n
      rw [if_pos rfl]
      have ready := (tile_end_ready p ops input tile b t (kAccum p ops input b tile) s ht starts).pc
      simpa only [if_neg (show ¬tile+1<p.k/32 by omega)] using ready
    · rw [if_neg last]
      exact ih (tile+1) _ (by omega) (by omega)
        (fun u hu => tile_next_start p ops input tile b u _ s (by omega) hu starts)

theorem k_loop_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b tile n t : Nat) (s : State α) (positive : 0<n) (count : tile+n=p.k/32)
    (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    (kLoopState p ops input b tile n s).indices t 13=some ((p.k/32 : Nat) : Int) := by
  induction n generalizing tile s with
  | zero => omega
  | succ n ih =>
    rw [kLoopState]
    by_cases last : n=0
    · subst n
      rw [if_pos rfl]
      have ready := (tile_end_ready p ops input tile b t (kAccum p ops input b tile) s ht starts).k
      simpa only [show tile+1=p.k/32 by omega] using ready
    · rw [if_neg last]
      exact ih (tile+1) _ (by omega) (by omega)
        (fun u hu => tile_next_start p ops input tile b u _ s (by omega) hu starts)

def wholeBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) : State α :=
  kLoopState p ops input b 0 (p.k/32) (afterFirstBarrier p ops b s)

theorem whole_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b : Nat) (s : State α) (hb : b<(geometry p).grid) (reads : Reads p input s)
    (hp : ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (fuel p).block s=
      some (wholeBlock p ops input b s) := by
  have positive : 0<p.k/32 := by have h := k_minimum p; omega
  change LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (2*(p.k/32)+1) s=_
  rw [initial_block_step p ops b (2*(p.k/32)) s hb hp]
  exact k_loop_run p ops input b 0 (p.k/32) _ positive (by omega)
    (after_first_reads p ops b s input reads) (fun t ht => after_first_staging_start p ops b t s ht)
    (fun bank hbank t ht e he => first_matrix_accumulators p ops b s bank t e hbank ht he)

theorem whole_block_halt (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b) :
    (wholeBlock p ops input b s).pc t=haltPC p := by
  have positive : 0<p.k/32 := by have h := k_minimum p; omega
  exact k_loop_halt p ops input b 0 (p.k/32) t _ positive (by omega) ht
    (fun u hu => after_first_staging_start p ops b u s hu)

#print axioms k_loop_run
#print axioms k_loop_halt
#print axioms k_loop_index
#print axioms whole_block_run
#print axioms whole_block_halt
end LarkNativeAwqGemm
