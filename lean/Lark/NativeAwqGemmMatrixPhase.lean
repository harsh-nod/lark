import Lark.NativeAwqGemmMatrixPass

/-! Both actual K16 passes of one K32 source iteration. All 8/16 native
matrix instructions execute with the original warp fuel and source order. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold blockOperands matrixState matrixBankState matrixFold matrixPassState

def matrixPhaseState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) : State α :=
  matrixPassState p ops input tile b 1 (matrixPassResult p ops input tile b 0 acc)
    (matrixPassState p ops input tile b 0 acc s)

def matrixPhaseResult (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) : Nat → Nat → Nat → α :=
  matrixPassResult p ops input tile b 1 (matrixPassResult p ops input tile b 0 acc)

theorem matrix_phase_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) :
    (matrixPhaseState p ops input tile b acc s).memory=s.memory ∧
      (matrixPhaseState p ops input tile b acc s).indices=s.indices ∧
        (matrixPhaseState p ops input tile b acc s).epochs=s.epochs := by
  have first := matrix_pass_frames p ops input tile b 0 acc s
  have second := matrix_pass_frames p ops input tile b 1 (matrixPassResult p ops input tile b 0 acc)
    (matrixPassState p ops input tile b 0 acc s)
  exact ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2.trans first.2.2⟩

theorem matrix_phase_regs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (bank t e : Nat)
    (hb : bank<banks p) (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (matrixPhaseState p ops input tile b acc s).regs t (bank*4+e)=some (matrixPhaseResult p ops input tile b acc bank t e) :=
  matrix_pass_regs p ops input tile b 1 (matrixPassResult p ops input tile b 0 acc)
    (matrixPassState p ops input tile b 0 acc s) bank t e hb ht he

theorem matrix_phase_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (t : Nat)
    (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile 0 0 u s) :
    (matrixPhaseState p ops input tile b acc s).pc t=47+14*banks p := by
  have second := matrix_pass_pc p ops input tile b 1 (matrixPassResult p ops input tile b 0 acc)
    (matrixPassState p ops input tile b 0 acc s) t ht
    (fun u hu => matrix_pass_next_entry p ops input tile b acc s u hu entries)
  have arithmetic : passPC p 1+4+5*banks p=47+14*banks p := by unfold passPC middleBarrier; omega
  rw [arithmetic] at second
  exact second

theorem matrix_phase_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b extra : Nat) (acc : Nat → Nat → Nat → α) (s : State α)
    (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile 0 0 t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (extra+2*banks p) s=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) extra
        (matrixPhaseState p ops input tile b acc s) := by
  rewrite [show extra+2*banks p=(extra+banks p)+banks p by omega,
    matrix_pass_run p ops input tile b 0 (extra+banks p) acc s (by decide) reads entries hc]
  exact matrix_pass_run p ops input tile b 1 extra (matrixPassResult p ops input tile b 0 acc)
    (matrixPassState p ops input tile b 0 acc s) (by decide)
    (tile_reads_of_memory p ops input tile b s _ reads (matrix_pass_frames p ops input tile b 0 acc s).1)
    (fun t ht => matrix_pass_next_entry p ops input tile b acc s t ht entries)
    (fun bank hb t ht e he => matrix_pass_regs p ops input tile b 0 acc s bank t e hb ht he)

theorem matrix_phase_fixed_fuel (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α)
    (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile 0 0 t s)
    (hc : ∀ bank, bank<banks p → ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc bank t e)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) (fuel p).warp s=
      LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) 1
        (matrixPhaseState p ops input tile b acc s) := by
  have count : (fuel p).warp=1+2*banks p := by
    rcases tile_cases p with hn | hn <;> simp [fuel,banks,hn]
  rw [count]
  exact matrix_phase_run p ops input tile b 1 acc s reads entries hc

#print axioms matrix_phase_frames
#print axioms matrix_phase_regs
#print axioms matrix_phase_pc
#print axioms matrix_phase_run
#print axioms matrix_phase_fixed_fuel
end LarkNativeAwqGemm
