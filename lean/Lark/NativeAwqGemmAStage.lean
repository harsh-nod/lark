import Lark.NativeAwqGemmALoop

/-! Complete guarded A-staging phase of the source, from the resumed first
barrier to B staging. Both paths retain their exact scalar instruction counts. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState

theorem a_element_init_site (p : Shape) : (program p)[firstBarrier p+1]?=some (ix 14 (c 0)) := by
  rw [show firstBarrier p+1=16+4*banks p+0 by unfold firstBarrier; omega,staging_site p 0 (by decide)]
  rfl

theorem a_row_guard_site (p : Shape) : (program p)[firstBarrier p+2]?=
    some (.scalar (.branch (.lt (v 6) (c p.m)) (firstBarrier p+8))) := by
  rw [show firstBarrier p+2=16+4*banks p+1 by unfold firstBarrier; omega,staging_site p 1 (by decide)]
  rfl

def aEntryState (p : Shape) (t : Nat) (zero : Bool) (s : State α) : State α :=
  advance (setIndex s t 14 0 (firstBarrier p+2)) t (aLoopPC p zero)

theorem a_entry_eq (p : Shape) (ops : Ops α) (t extra : Nat) (zero : Bool) (s : State α)
    (setup : SetupIndices p t s) (hp : s.pc t=firstBarrier p+1)
    (guard : zero=false ↔ inputRow p t<p.m) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+2) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aEntryState p t zero s) := by
  let initialized := setIndex s t 14 0 (firstBarrier p+2)
  have initPC : initialized.pc t=firstBarrier p+2 := by simp [initialized,setIndex,advance]
  have rowIndex : evalIndex (geometry p) t initialized (v 6)=some ((inputRow p t : Nat) : Int) := by
    simpa [initialized,v,evalIndex,setIndex,advance] using setup.aRow
  have mBound : p.m<2147483648 := by have bound := (scalar_parameter_bounds p).1; omega
  have initStep := execute_index_of ops p t 14 (firstBarrier p+2) (c 0) s 0
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have branchStep : execute ops (layout p) (geometry p) t
      (.branch (.lt (v 6) (c p.m)) (firstBarrier p+8)) initialized=some (aEntryState p t zero s) := by
    cases zero with
    | false =>
      have valid := guard.mp rfl
      have pred := eval_int_lt_true (geometry p) t initialized (v 6) (c p.m) (inputRow p t : Int) (p.m : Int)
        rowIndex (eval_nat_const _ _ _ _ mBound) (by omega)
      have step := execute_branch_true ops p t (firstBarrier p+8) (.lt (v 6) (c p.m)) initialized pred
      rw [initPC] at step
      exact step
    | true =>
      have invalid : ¬inputRow p t<p.m := by intro valid; have impossible := guard.mpr valid; cases impossible
      have pred := eval_int_lt_false (geometry p) t initialized (v 6) (c p.m) (inputRow p t : Int) (p.m : Int)
        rowIndex (eval_nat_const _ _ _ _ mBound) (by omega)
      exact execute_branch_false ops p t (firstBarrier p+8) (.lt (v 6) (c p.m)) initialized pred
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (firstBarrier p+1) (extra+1) _ s initialized (a_element_init_site p) hp initStep]
  exact scalar_step p ops t (firstBarrier p+2) extra _ initialized _ (a_row_guard_site p) initPC branchStep

theorem a_entry_indices (p : Shape) (tile t : Nat) (zero : Bool) (s : State α)
    (setup : SetupIndices p t s) (hk : s.indices t 13=some (tile : Int)) :
    AIndices p tile t 0 (aEntryState p t zero s) := by
  let initialized := setIndex s t 14 0 (firstBarrier p+2)
  have h : AIndices p tile t 0 initialized := {
    setup := setIndex_setup p t 14 (firstBarrier p+2) 0 s setup (by decide)
    k := by simpa [initialized,setIndex,advance] using hk
    element := by simp [initialized,setIndex,advance] }
  exact a_indices_of_indices p tile t 0 initialized _ h rfl

theorem a_entry_reads (p : Shape) (input : Nat → Nat → α) (t : Nat) (zero : Bool) (s : State α)
    (reads : Reads p input s) : Reads p input (aEntryState p t zero s) := reads

theorem a_entry_pc (p : Shape) (t : Nat) (zero : Bool) (s : State α) :
    (aEntryState p t zero s).pc t=aLoopPC p zero := by simp [aEntryState,advance]

def aStageBody (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (zero : Bool) (s : State α) : State α :=
  aLoopState p ops input tile t zero 0 8 (aEntryState p t zero s)

def aStageState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) : State α :=
  if inputRow p t<p.m then
    advance (advance (aStageBody p ops input tile t false s) t (aExitPC p false)) t (firstBarrier p+12)
  else advance (aStageBody p ops input tile t true s) t (aExitPC p true)

def aStageCost (p : Shape) (t : Nat) : Nat := if inputRow p t<p.m then 36 else 35

theorem a_stage_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t extra : Nat) (s : State α) (hk : tile<p.k/32) (setup : SetupIndices p t s)
    (ki : s.indices t 13=some (tile : Int)) (reads : Reads p input s) (hp : s.pc t=firstBarrier p+1) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+aStageCost p t) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aStageState p ops input tile t s) := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageCost,if_pos valid,aStageState,if_pos valid]
    let entered := aEntryState p t false s
    let looped := aStageBody p ops input tile t false s
    have ready : AIndices p tile t 0 entered := a_entry_indices p tile t false s setup ki
    have entryPC : entered.pc t=aLoopPC p false := a_entry_pc p t false s
    have loopReady : AIndices p tile t 8 looped := a_loop_indices p ops input tile t 0 8 false entered ready
    have loopPC : looped.pc t=aLoopPC p false := a_loop_pc p ops input tile t 0 8 false entered entryPC
    rewrite [show extra+36=(extra+34)+2 by omega,a_entry_eq p ops t (extra+34) false s setup hp (by simp [valid])]
    rewrite [show extra+34=(extra+2)+4*8 by omega,
      a_loop_eq p ops input tile t 0 8 (extra+2) false entered hk (by decide) ready
        (a_entry_reads p input t false s reads) (by intro _; exact valid) entryPC]
    change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+2) looped=_
    rewrite [show extra+2=(extra+1)+1 by omega,a_loop_exit_eq p ops tile t (extra+1) false looped loopReady loopPC]
    exact a_exit_jump_eq p ops t extra _ (by simp [aExitPC,advance])
  · rw [aStageCost,if_neg valid,aStageState,if_neg valid]
    let entered := aEntryState p t true s
    let looped := aStageBody p ops input tile t true s
    have ready : AIndices p tile t 0 entered := a_entry_indices p tile t true s setup ki
    have entryPC : entered.pc t=aLoopPC p true := a_entry_pc p t true s
    have loopReady : AIndices p tile t 8 looped := a_loop_indices p ops input tile t 0 8 true entered ready
    have loopPC : looped.pc t=aLoopPC p true := a_loop_pc p ops input tile t 0 8 true entered entryPC
    rewrite [show extra+35=(extra+33)+2 by omega,a_entry_eq p ops t (extra+33) true s setup hp (by simp [valid])]
    rewrite [show extra+33=extra+1+4*8 by omega,
      a_loop_eq p ops input tile t 0 8 (extra+1) true entered hk (by decide) ready
        (a_entry_reads p input t true s reads) (by intro impossible; cases impossible) entryPC]
    exact a_loop_exit_eq p ops tile t extra true looped loopReady loopPC

theorem a_stage_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (aStageState p ops input tile t s).pc t=firstBarrier p+12 := by
  by_cases valid : inputRow p t<p.m <;> simp [aStageState,valid,aExitPC,advance]

theorem a_stage_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (setup : SetupIndices p t s) (ki : s.indices t 13=some (tile : Int)) :
    AIndices p tile t 8 (aStageState p ops input tile t s) := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid]
    exact a_indices_of_indices p tile t 8 (aStageBody p ops input tile t false s) _
      (a_loop_indices p ops input tile t 0 8 false (aEntryState p t false s) (a_entry_indices p tile t false s setup ki)) rfl
  · rw [aStageState,if_neg valid]
    exact a_indices_of_indices p tile t 8 (aStageBody p ops input tile t true s) _
      (a_loop_indices p ops input tile t 0 8 true (aEntryState p t true s) (a_entry_indices p tile t true s setup ki)) rfl

theorem a_stage_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t : Nat) (s : State α) (reads : Reads p input s) : Reads p input (aStageState p ops input tile t s) := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid]
    exact a_loop_reads p ops input tile t 0 8 false (aEntryState p t false s) (a_entry_reads p input t false s reads)
  · rw [aStageState,if_neg valid]
    exact a_loop_reads p ops input tile t 0 8 true (aEntryState p t true s) (a_entry_reads p input t true s reads)

theorem a_stage_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (aStageState p ops input tile t s).regs=s.regs ∧ (aStageState p ops input tile t s).epochs=s.epochs := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid]
    exact a_loop_frames p ops input tile t 0 8 false (aEntryState p t false s)
  · rw [aStageState,if_neg valid]
    exact a_loop_frames p ops input tile t 0 8 true (aEntryState p t true s)

theorem a_stage_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α) :
    (aStageState p ops input tile t s).trace.length=s.trace.length+(if inputRow p t<p.m then 16 else 8) := by
  by_cases valid : inputRow p t<p.m
  · rw [aStageState,if_pos valid,if_pos valid]
    exact a_loop_trace_length p ops input tile t 0 8 false (aEntryState p t false s)
  · rw [aStageState,if_neg valid,if_neg valid]
    exact a_loop_trace_length p ops input tile t 0 8 true (aEntryState p t true s)

#print axioms a_element_init_site
#print axioms a_row_guard_site
#print axioms a_entry_eq
#print axioms a_entry_indices
#print axioms a_entry_reads
#print axioms a_entry_pc
#print axioms a_stage_eq
#print axioms a_stage_pc
#print axioms a_stage_indices
#print axioms a_stage_reads
#print axioms a_stage_frames
#print axioms a_stage_trace_length
end LarkNativeAwqGemm
