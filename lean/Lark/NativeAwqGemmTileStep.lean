import Lark.NativeAwqGemmTailBlock

/-! One complete original K32 iteration, including both staging barriers,
both native matrix passes, K control, and final guarded outputs if last. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands
  matrixState matrixBankState matrixFold matrixPassState matrixPhaseState stagingFold stagingState
  outputRound outputStored outputLoop outputLane tailLane tailFold blockTail nextTile

def tileMatrix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) : State α :=
  matrixPhaseState p ops input tile b acc (afterMiddleBarrier p ops input tile b s)

def tileValues (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (t q : Nat) : α :=
  matrixPhaseResult p ops input tile b acc (q/4) t (q%4)

def tileEnd (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) : State α :=
  blockTail p ops tile b (tileValues p ops input tile b acc) (tileMatrix p ops input tile b acc s)

def tileNext (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) : State α :=
  nextTile p ops tile b (tileValues p ops input tile b acc) (tileMatrix p ops input tile b acc s)

theorem tile_matrix_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    TailEntry p tile t (tileMatrix p ops input tile b acc s) := by
  have ready := after_middle_ready p ops input tile b t s ht starts
  have frames := matrix_phase_frames p ops input tile b acc (afterMiddleBarrier p ops input tile b s)
  exact ⟨matrix_phase_pc p ops input tile b acc _ t ht (fun u hu => first_operand_entry p ops input tile b u s hu starts),
    setup_of_indices p t _ _ ready.2.setup frames.2.1,by rw [show (tileMatrix p ops input tile b acc s).indices=
      (afterMiddleBarrier p ops input tile b s).indices from frames.2.1]; exact ready.2.k⟩

theorem tile_matrix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t q : Nat) (acc : Nat → Nat → Nat → α) (s : State α)
    (ht : t∈blockThreads (geometry p) b) (hq : q<4*banks p) :
    (tileMatrix p ops input tile b acc s).regs t q=some (tileValues p ops input tile b acc t q) := by
  have result := matrix_phase_regs p ops input tile b acc (afterMiddleBarrier p ops input tile b s)
    (q/4) t (q%4) (by omega) ht (Nat.mod_lt _ (by decide))
  simpa only [show q/4*4+q%4=q by omega] using result

theorem tile_next_start (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (more : tile+1<p.k/32)
    (ht : t∈blockThreads (geometry p) b) (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    StagingStart p (tile+1) t (tileNext p ops input tile b acc s) :=
  next_tile_start p ops tile b t (tileValues p ops input tile b acc) _ more ht
    (fun u hu => tile_matrix_entry p ops input tile b u acc s hu starts)

theorem tile_next_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b bank t e : Nat) (acc : Nat → Nat → Nat → α) (s : State α)
    (hb : bank<banks p) (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (tileNext p ops input tile b acc s).regs t (bank*4+e)=
      some (matrixPhaseResult p ops input tile b acc bank t e) := by
  unfold tileNext nextTile
  change (blockTail p ops tile b (tileValues p ops input tile b acc) (tileMatrix p ops input tile b acc s)).regs t _=_
  rw [(block_tail_frames p ops tile b _ _).1]
  exact matrix_phase_regs p ops input tile b acc _ bank t e hb ht he

theorem tile_next_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (tileNext p ops input tile b acc s) := by
  unfold tileNext nextTile
  apply block_tail_reads p ops input tile b _ _
  unfold Reads
  rw [show (tileMatrix p ops input tile b acc s).memory=(afterMiddleBarrier p ops input tile b s).memory from
    (matrix_phase_frames p ops input tile b acc _).1]
  exact after_middle_reads p ops input tile b s reads

theorem tile_end_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    TailReady p tile t (tileEnd p ops input tile b acc s) :=
  block_tail_ready p ops tile b t (tileValues p ops input tile b acc) _ ht
    (fun u hu => tile_matrix_entry p ops input tile b u acc s hu starts)

theorem tile_matrix_tail_warp (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hk : tile<p.k/32)
    (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (fuel p).warp
      (afterMiddleBarrier p ops input tile b s)=some (tileEnd p ops input tile b acc s) := by
  rw [matrix_phase_fixed_fuel p ops input tile b acc _ (after_middle_tiles p ops input tile b s)
    (fun t ht => first_operand_entry p ops input tile b t s ht starts)
    (fun bank hb t ht e he => by rw [(after_middle_frames p ops input tile b s).1]; exact hc bank hb t ht e he)]
  exact block_tail_warp_run p ops tile b (tileValues p ops input tile b acc) _ hk
    (fun t ht => tile_matrix_entry p ops input tile b t acc s ht starts)
    (fun t ht q hq => tile_matrix_values p ops input tile b t q acc s ht hq)

theorem tile_run_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b extra : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hk : tile<p.k/32)
    (reads : Reads p input s) (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (extra+2) s=
      if tile+1<p.k/32 then LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b extra
        (tileNext p ops input tile b acc s) else some (tileEnd p ops input tile b acc s) := by
  rw [show extra+2=(extra+1)+1 by omega,block_staging_step p ops input tile b (extra+1) s hk reads starts]
  have warp := tile_matrix_tail_warp p ops input tile b acc s hk starts hc
  have waves : (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun state w => LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
        (warpThreads (geometry p) b w) (fuel p).warp state) (afterMiddleBarrier p ops input tile b s)=
          some (tileEnd p ops input tile b acc s) := by
    have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=1 := by
      change ((64+64-1)/64 : Nat)=1
      decide
    rw [count]
    change ([0] : List Nat).foldlM _ _=some (tileEnd p ops input tile b acc s)
    rw [LarkMFMA.foldlM_singleton,native_warp_threads]
    exact warp
  have converged := block_tail_converged p ops tile b (tileValues p ops input tile b acc)
    (tileMatrix p ops input tile b acc s) (fun t ht => tile_matrix_entry p ops input tile b t acc s ht starts)
  change LarkMFMA.converged (program p) (blockThreads (geometry p) b) (tileEnd p ops input tile b acc s)=_ at converged
  by_cases more : tile+1<p.k/32
  · simp only [LarkMFMA.runBlock,waves,bind,pure,Option.bind,converged,if_pos more,ite_true]
    unfold tileNext nextTile tileEnd
    rfl
  · simp [LarkMFMA.runBlock,waves,converged,more]

#print axioms tile_matrix_entry
#print axioms tile_matrix_values
#print axioms tile_next_start
#print axioms tile_next_accumulator
#print axioms tile_next_reads
#print axioms tile_end_ready
#print axioms tile_matrix_tail_warp
#print axioms tile_run_step
end LarkNativeAwqGemm
