import Lark.NativeAwqGemmMatrixPhase

/-! The full source's staging visit and both native K16 passes are connected
through the actual middle-barrier state. K/output continuation is retained. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands matrixState matrixBankState matrixFold matrixPassState matrixPhaseState stagingFold stagingState

theorem first_matrix_accumulators (p : Shape) (ops : Ops α) (b : Nat) (s : State α)
    (bank t e : Nat) (hb : bank<banks p) (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (afterFirstBarrier p ops b s).regs t (bank*4+e)=some (ops.literal 0 1) :=
  (block_prefix_ready p ops b t s ht).accumulator (bank*4+e) (by omega)

theorem matrix_iteration (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b extra : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hk : tile<p.k/32)
    (reads : Reads p input s) (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    let mid := afterMiddleBarrier p ops input tile b s
    let final := matrixPhaseState p ops input tile b acc mid
    (LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (extra+1) s=
      LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b extra mid) ∧
    (LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (fuel p).warp mid=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) 1 final) ∧
    (∀ t∈blockThreads (geometry p) b, final.pc t=47+14*banks p) ∧
    (∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 →
      final.regs t (bank*4+e)=some (matrixPhaseResult p ops input tile b acc bank t e)) ∧
    final.memory=mid.memory ∧ final.indices=mid.indices ∧ final.epochs=mid.epochs ∧ Reads p input final := by
  let mid := afterMiddleBarrier p ops input tile b s
  let final := matrixPhaseState p ops input tile b acc mid
  have entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile 0 0 t mid :=
    fun t ht => first_operand_entry p ops input tile b t s ht starts
  have oldAcc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → mid.regs t (bank*4+e)=some (acc bank t e) := by
    intro bank hb t ht e he
    rw [(after_middle_frames p ops input tile b s).1]
    exact hc bank hb t ht e he
  have frames := matrix_phase_frames p ops input tile b acc mid
  have finalReads : Reads p input final := by
    unfold Reads
    rw [frames.1]
    exact after_middle_reads p ops input tile b s reads
  exact ⟨block_staging_step p ops input tile b extra s hk reads starts,
    matrix_phase_fixed_fuel p ops input tile b acc mid (after_middle_tiles p ops input tile b s) entries oldAcc,
    fun t ht => matrix_phase_pc p ops input tile b acc mid t ht entries,
    fun bank hb t ht e he => matrix_phase_regs p ops input tile b acc mid bank t e hb ht he,
    frames.1,frames.2.1,frames.2.2,finalReads⟩

#print axioms first_matrix_accumulators
#print axioms matrix_iteration
end LarkNativeAwqGemm
