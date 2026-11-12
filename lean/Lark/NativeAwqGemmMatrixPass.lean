import Lark.NativeAwqGemmMMAFold

/-! All four/eight native MFMA banks of one K16 source pass, including its
exact continuation PC and every updated accumulator element. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands matrixState matrixBankState matrixFold

def matrixPassState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) (s : State α) : State α :=
  matrixFold p ops input tile b half acc 0 (banks p) s

def matrixPassResult (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) (bank t e : Nat) : α :=
  matrixValue p ops input tile b half bank (acc bank) t e

theorem matrix_pass_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) (s : State α) :
    (matrixPassState p ops input tile b half acc s).memory=s.memory ∧
      (matrixPassState p ops input tile b half acc s).indices=s.indices ∧
        (matrixPassState p ops input tile b half acc s).epochs=s.epochs :=
  matrix_fold_frames p ops input tile b half 0 (banks p) acc s

theorem matrix_pass_regs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (bank t e : Nat)
    (hb : bank<banks p) (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (matrixPassState p ops input tile b half acc s).regs t (bank*4+e)=
      some (matrixPassResult p ops input tile b half acc bank t e) :=
  matrix_fold_regs p ops input tile b half 0 (banks p) bank acc s t e (by omega) (by omega) hb ht he

theorem matrix_pass_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (t : Nat)
    (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile half 0 u s) :
    (matrixPassState p ops input tile b half acc s).pc t=passPC p half+4+5*banks p := by
  have nonzero : banks p≠0 := by rcases banks_cases p with hb | hb <;> omega
  have final := matrix_fold_entries p ops input tile b half 0 (banks p) acc s (by omega) entries t ht
  have pc := final.pc
  simpa only [matrixPassState,Nat.zero_add,operandLaneStart,if_neg nonzero,operandStart,Bool.false_eq_true,ite_false] using pc

theorem matrix_pass_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half extra : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (hh : half<2)
    (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half 0 t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (extra+banks p) s=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) extra
        (matrixPassState p ops input tile b half acc s) :=
  matrix_fold_run p ops input tile b half 0 (banks p) extra acc s hh (by omega) reads entries
    (fun bank hlo hb => hc bank hb)

theorem matrix_pass_next_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (t : Nat)
    (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile 0 0 u s) :
    OperandEntry p ops input tile 1 0 t (matrixPassState p ops input tile b 0 acc s) := by
  exact {pc := by
           rw [matrix_pass_pc p ops input tile b 0 acc s t ht entries]
           unfold operandLaneStart passPC
           simp only [ite_true]
           omega
         lane := by rw [(matrix_pass_frames p ops input tile b 0 acc s).2.1]; exact (entries t ht).lane
         a := by intro nonzero; exact False.elim (nonzero rfl)}

#print axioms matrix_pass_frames
#print axioms matrix_pass_regs
#print axioms matrix_pass_pc
#print axioms matrix_pass_run
#print axioms matrix_pass_next_entry
end LarkNativeAwqGemm
