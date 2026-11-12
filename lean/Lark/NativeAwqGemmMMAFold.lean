import Lark.NativeAwqGemmMMABank

/-! Induction over every native matrix bank in one K16 pass. Unprocessed
accumulators retain their old values until their own source instruction. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands matrixState matrixBankState

def matrixFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) : Nat → Nat → State α → State α
  | _,0,s => s
  | bank,n+1,s => matrixFold p ops input tile b half acc (bank+1) n
      (matrixBankState p ops input tile b half bank (acc bank) s)

theorem matrix_fold_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n : Nat) (acc : Nat → Nat → Nat → α) (s : State α) :
    (matrixFold p ops input tile b half acc bank n s).memory=s.memory ∧
      (matrixFold p ops input tile b half acc bank n s).indices=s.indices ∧
        (matrixFold p ops input tile b half acc bank n s).epochs=s.epochs := by
  induction n generalizing bank s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    have one := matrix_bank_frames p ops input tile b half bank (acc bank) s
    have rest := ih (bank+1) (matrixBankState p ops input tile b half bank (acc bank) s)
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem matrix_fold_other_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n otherBank : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (t e : Nat)
    (outside : ¬(bank≤otherBank ∧ otherBank<bank+n)) (hb : otherBank<banks p) (he : e<4) :
    (matrixFold p ops input tile b half acc bank n s).regs t (otherBank*4+e)=s.regs t (otherBank*4+e) := by
  induction n generalizing bank s with
  | zero => rfl
  | succ n ih =>
    rw [matrixFold]
    have rest := ih (bank+1) (matrixBankState p ops input tile b half bank (acc bank) s) (by omega)
    exact rest.trans (matrix_bank_other_accumulator p ops input tile b half bank otherBank (acc bank) s t e (by omega) hb he)

theorem matrix_fold_regs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n resultBank : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (t e : Nat)
    (hlo : bank≤resultBank) (hhi : resultBank<bank+n) (hb : resultBank<banks p)
    (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (matrixFold p ops input tile b half acc bank n s).regs t (resultBank*4+e)=
      some (matrixValue p ops input tile b half resultBank (acc resultBank) t e) := by
  induction n generalizing bank s with
  | zero => omega
  | succ n ih =>
    rw [matrixFold]
    by_cases same : resultBank=bank
    · subst resultBank
      have rest := matrix_fold_other_accumulator p ops input tile b half (bank+1) n bank acc
        (matrixBankState p ops input tile b half bank (acc bank) s) t e (by omega) hb he
      exact rest.trans (matrix_bank_regs p ops input tile b half bank (acc bank) s t e ht he)
    · exact ih (bank+1) (matrixBankState p ops input tile b half bank (acc bank) s) (by omega) (by omega)

theorem matrix_fold_entries (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hn : bank+n≤banks p)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank t s) :
    ∀ t∈blockThreads (geometry p) b,
      OperandEntry p ops input tile half (bank+n) t (matrixFold p ops input tile b half acc bank n s) := by
  induction n generalizing bank s with
  | zero => exact entries
  | succ n ih =>
    have next := ih (bank+1) (matrixBankState p ops input tile b half bank (acc bank) s) (by omega)
      (fun t ht => matrix_bank_next_entry p ops input tile b half bank (acc bank) s t ht (by omega) entries)
    simpa only [matrixFold,show (bank+1)+n=bank+(n+1) by omega] using next

theorem matrix_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n extra : Nat) (acc : Nat → Nat → Nat → α) (s : State α)
    (hh : half<2) (hn : bank+n≤banks p) (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank t s)
    (hc : ∀ j, bank≤j → j<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (j*4+e)=some (acc j t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (extra+n) s=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) extra
        (matrixFold p ops input tile b half acc bank n s) := by
  induction n generalizing bank extra s with
  | zero => rfl
  | succ n ih =>
    have bankBound : bank<banks p := by omega
    rewrite [show extra+(n+1)=(extra+n)+1 by omega,
      native_bank_step p ops input tile b half bank (extra+n) (acc bank) s hh bankBound reads entries
        (hc bank (by omega) bankBound)]
    apply ih (bank+1) extra (matrixBankState p ops input tile b half bank (acc bank) s) (by omega)
      (tile_reads_of_memory p ops input tile b s _ reads (matrix_bank_frames p ops input tile b half bank (acc bank) s).1)
      (fun t ht => matrix_bank_next_entry p ops input tile b half bank (acc bank) s t ht bankBound entries)
    intro j hj hbank t ht e he
    rw [matrix_bank_other_accumulator p ops input tile b half bank j (acc bank) s t e (by omega) hbank he]
    exact hc j (by omega) hbank t ht e he

#print axioms matrix_fold_frames
#print axioms matrix_fold_other_accumulator
#print axioms matrix_fold_regs
#print axioms matrix_fold_entries
#print axioms matrix_fold_run
end LarkNativeAwqGemm
