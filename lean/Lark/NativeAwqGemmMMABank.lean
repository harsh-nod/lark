import Lark.NativeAwqGemmMMAValues

/-! One actual source bank: all native operand loads, convergence, then the
unchanged MFMA instruction. Other accumulator banks and A operands survive. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands matrixState

def matrixBankState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) : State α :=
  matrixState p ops input tile b half bank acc (blockOperands p ops input tile b half bank s)

theorem native_bank_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank extra : Nat) (acc : Nat → Nat → α) (s : State α) (hh : half<2) (hb : bank<banks p)
    (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank t s)
    (hc : ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (extra+1) s=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) extra
        (matrixBankState p ops input tile b half bank acc s) := by
  have ready := fun t ht => block_operands_ready p ops input tile b half bank t s ht entries
  have accumulator : ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 →
      (blockOperands p ops input tile b half bank s).regs t (bank*4+e)=some (acc t e) := by
    intro t ht e he
    rw [block_operands_accumulator p ops input tile b half bank t (bank*4+e) s (by omega)]
    exact hc t ht e he
  exact LarkMFMA.runWarp_matrix_step ops (layout p) (geometry p) (fuel p) (program p) _ extra s
    (blockOperands p ops input tile b half bank s) (matrixBankState p ops input tile b half bank acc s)
    (block_operands_run p ops input tile b half bank s hh hb reads entries)
    (block_operands_converged p ops input tile b half bank s hh hb entries)
    (native_matrix_execute p ops input tile b half bank acc _ hh hb ready accumulator)

theorem matrix_bank_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) :
    (matrixBankState p ops input tile b half bank acc s).memory=s.memory ∧
      (matrixBankState p ops input tile b half bank acc s).indices=s.indices ∧
        (matrixBankState p ops input tile b half bank acc s).epochs=s.epochs := by
  have matrix := matrix_state_frames p ops input tile b half bank acc (blockOperands p ops input tile b half bank s)
  have loads := block_operands_frames p ops input tile b half bank s
  exact ⟨matrix.1.trans loads.1,matrix.2.2.1.trans loads.2.1,matrix.2.2.2.trans loads.2.2⟩

theorem matrix_bank_regs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t e : Nat)
    (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (matrixBankState p ops input tile b half bank acc s).regs t (bank*4+e)=
      some (matrixValue p ops input tile b half bank acc t e) :=
  matrix_state_regs p ops input tile b half bank acc _ t e ht he

theorem matrix_bank_other_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank otherBank : Nat) (acc : Nat → Nat → α) (s : State α) (t e : Nat)
    (different : otherBank≠bank) (hother : otherBank<banks p) (he : e<4) :
    (matrixBankState p ops input tile b half bank acc s).regs t (otherBank*4+e)=s.regs t (otherBank*4+e) := by
  unfold matrixBankState
  rw [matrix_state_regs_other p ops input tile b half bank acc _ t (otherBank*4+e) (by omega)]
  exact block_operands_accumulator p ops input tile b half bank t (otherBank*4+e) s (by omega)

theorem matrix_bank_a_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t e : Nat)
    (ht : t∈blockThreads (geometry p) b) (hb : bank<banks p) (he : e<4)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank u s) :
    (matrixBankState p ops input tile b half bank acc s).regs t (leftBase p half+e)=some (aOperand p ops input tile t half e) := by
  have lower : 4*banks p≤leftBase p half := operand_base_lower p half 0 true
  unfold matrixBankState
  rw [matrix_state_regs_other p ops input tile b half bank acc _ t (leftBase p half+e) (by omega)]
  exact (block_operands_ready p ops input tile b half bank t s ht entries).a e he

theorem matrix_bank_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t : Nat)
    (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank u s) :
    (matrixBankState p ops input tile b half bank acc s).pc t=matrixPC p half bank+1 := by
  unfold matrixBankState
  rw [matrix_state_pc,if_pos ht,(block_operands_ready p ops input tile b half bank t s ht entries).pc]

theorem matrix_bank_next_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t : Nat)
    (ht : t∈blockThreads (geometry p) b) (hb : bank<banks p)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank u s) :
    OperandEntry p ops input tile half (bank+1) t (matrixBankState p ops input tile b half bank acc s) := by
  have frame := matrix_bank_frames p ops input tile b half bank acc s
  exact {pc := by
           rw [matrix_bank_pc p ops input tile b half bank acc s t ht entries]
           unfold operandLaneStart operandStart matrixPC
           rw [if_neg (by omega : bank+1≠0)]
           simp only [Bool.false_eq_true,ite_false]
           omega
         lane := by rw [frame.2.1]; exact (entries t ht).lane
         a := by intro nonzero e he; exact matrix_bank_a_value p ops input tile b half bank acc s t e ht hb he entries}

#print axioms native_bank_step
#print axioms matrix_bank_frames
#print axioms matrix_bank_regs
#print axioms matrix_bank_other_accumulator
#print axioms matrix_bank_a_value
#print axioms matrix_bank_pc
#print axioms matrix_bank_next_entry
end LarkNativeAwqGemm
