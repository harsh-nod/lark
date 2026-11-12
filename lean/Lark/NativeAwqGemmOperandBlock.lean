import Lark.NativeAwqGemmOperandFold

/-! The actual wave64 operand-loading visit converges at each native MFMA.
The first such visit follows the source's proved middle-barrier resumption. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState operandFold

def blockOperands (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (s : State α) : State α :=
  operandFold p ops input tile half bank (blockThreads (geometry p) b) s

theorem block_operands_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank u s) :
    OperandReady p ops input tile half bank t (blockOperands p ops input tile b half bank s) :=
  operand_fold_ready p ops input tile half bank t _ s (block_threads_nodup p b) ht entries

theorem block_operands_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (s : State α) (hh : half<2) (hbank : bank<banks p)
    (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank t s) :
    (blockThreads (geometry p) b).foldlM
      (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state) s=
        some (blockOperands p ops input tile b half bank s) :=
  operand_fold_run p ops input tile b half bank _ s hh hbank (block_threads_nodup p b)
    (fun t ht => block_thread_block p b t ht) reads entries

theorem block_operands_converged (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (s : State α) (hh : half<2) (hbank : bank<banks p)
    (entries : ∀ t∈blockThreads (geometry p) b, OperandEntry p ops input tile half bank t s) :
    LarkMFMA.converged (program p) (blockThreads (geometry p) b) (blockOperands p ops input tile b half bank s)=some .matrix := by
  have head : (blockThreads (geometry p) b).head?=some (b*64) := rfl
  have headMember : b*64∈blockThreads (geometry p) b :=
    List.mem_map.mpr ⟨0,by change 0∈List.range 64; decide,rfl⟩
  have headPC := (block_operands_ready p ops input tile b half bank (b*64) s headMember entries).pc
  have allPC : (blockThreads (geometry p) b).all
      (fun t => (blockOperands p ops input tile b half bank s).pc t==(blockOperands p ops input tile b half bank s).pc (b*64))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    rw [(block_operands_ready p ops input tile b half bank t s ht entries).pc,headPC]
    simp
  simp only [LarkMFMA.converged,head,bind,pure,Option.bind,allPC,ite_true]
  simp only [LarkMFMA.parked,headPC,matrix_instruction_site p half bank hh hbank]

theorem block_operands_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (s : State α) :
    (blockOperands p ops input tile b half bank s).memory=s.memory ∧
      (blockOperands p ops input tile b half bank s).indices=s.indices ∧
        (blockOperands p ops input tile b half bank s).epochs=s.epochs :=
  operand_fold_frames p ops input tile half bank _ s

theorem block_operands_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank u r : Nat) (s : State α) (hr : r<4*banks p) :
    (blockOperands p ops input tile b half bank s).regs u r=s.regs u r :=
  operand_fold_accumulator p ops input tile half bank u r _ s hr

theorem first_operand_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    OperandEntry p ops input tile 0 0 t (afterMiddleBarrier p ops input tile b s) := by
  have ready := after_middle_ready p ops input tile b t s ht starts
  exact {pc := by simpa [operandLaneStart,passPC] using ready.1
         lane := ready.2.setup.header.lane
         a := by intro nonzero; exact False.elim (nonzero rfl)}

theorem first_operands_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s) :
    (blockThreads (geometry p) b).foldlM
      (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state)
        (afterMiddleBarrier p ops input tile b s)=
          some (blockOperands p ops input tile b 0 0 (afterMiddleBarrier p ops input tile b s)) := by
  have bank : 0<banks p := by rcases banks_cases p with hb | hb <;> omega
  exact block_operands_run p ops input tile b 0 0 _ (by decide) bank (after_middle_tiles p ops input tile b s)
    (fun t ht => first_operand_entry p ops input tile b t s ht starts)

#print axioms block_operands_ready
#print axioms block_operands_run
#print axioms block_operands_converged
#print axioms block_operands_frames
#print axioms block_operands_accumulator
#print axioms first_operand_entry
#print axioms first_operands_run
end LarkNativeAwqGemm
