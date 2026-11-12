import Lark.NativeAwqGemmARound

/-! Induction over all eight source A-staging iterations, followed by the
actual failed loop test and the valid-row path's join jump. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def aLoopState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (zero : Bool) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | e,n+1,s => aLoopState p ops input tile t zero (e+1) n (aRoundState p ops input tile t e zero s)

theorem a_loop_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) (h : AIndices p tile t e s) :
    AIndices p tile t (e+n) (aLoopState p ops input tile t zero e n s) := by
  induction n generalizing e s with
  | zero => exact h
  | succ n ih =>
    have next := ih (e+1) (aRoundState p ops input tile t e zero s) (a_round_indices p ops input tile t e zero s h)
    simpa only [aLoopState,show (e+1)+n=e+(n+1) by omega] using next

theorem a_loop_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) (h : Reads p input s) :
    Reads p input (aLoopState p ops input tile t zero e n s) := by
  induction n generalizing e s with
  | zero => exact h
  | succ n ih => exact ih (e+1) _ (a_round_reads p ops input tile t e zero s h)

theorem a_loop_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) (hp : s.pc t=aLoopPC p zero) :
    (aLoopState p ops input tile t zero e n s).pc t=aLoopPC p zero := by
  induction n generalizing e s with
  | zero => exact hp
  | succ n ih => exact ih (e+1) _ (a_round_pc p ops input tile t e zero s)

theorem a_loop_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) :
    (aLoopState p ops input tile t zero e n s).regs=s.regs ∧
      (aLoopState p ops input tile t zero e n s).epochs=s.epochs := by
  induction n generalizing e s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have round := a_round_frames p ops input tile t e zero s
    have rest := ih (e+1) (aRoundState p ops input tile t e zero s)
    exact ⟨rest.1.trans round.1,rest.2.trans round.2⟩

theorem a_loop_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n extra : Nat) (zero : Bool) (s : State α)
    (hk : tile<p.k/32) (hn : e+n≤8) (h : AIndices p tile t e s) (reads : Reads p input s)
    (hr : zero=false → inputRow p t<p.m) (hp : s.pc t=aLoopPC p zero) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4*n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra
        (aLoopState p ops input tile t zero e n s) := by
  induction n generalizing e extra s with
  | zero => rfl
  | succ n ih =>
    rewrite [show extra+4*(n+1)=(extra+4*n)+4 by omega,
      a_round_eq p ops input tile t e (extra+4*n) zero s hk (by omega) h reads hr hp]
    exact ih (e+1) extra (aRoundState p ops input tile t e zero s) (by omega)
      (a_round_indices p ops input tile t e zero s h) (a_round_reads p ops input tile t e zero s reads)
      (a_round_pc p ops input tile t e zero s)

theorem a_loop_exit_eq (p : Shape) (ops : Ops α) (tile t extra : Nat) (zero : Bool) (s : State α)
    (h : AIndices p tile t 8 s) (hp : s.pc t=aLoopPC p zero) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (advance s t (aExitPC p zero)) := by
  have predicate := eval_int_lt_false (geometry p) t s (v 14) (c 8) 8 8 h.element
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  exact scalar_step p ops t (aLoopPC p zero) extra _ s _ (a_loop_test_site p zero) hp
    (execute_branch_false ops p t (aExitPC p zero) (.lt (v 14) (c 8)) s predicate)

theorem a_exit_jump_site (p : Shape) : (program p)[firstBarrier p+7]?=
    some (.scalar (.jump (firstBarrier p+12))) := by
  rw [show firstBarrier p+7=16+4*banks p+6 by unfold firstBarrier; omega,staging_site p 6 (by decide)]
  rfl

theorem a_exit_jump_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t=firstBarrier p+7) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (advance s t (firstBarrier p+12)) :=
  scalar_step p ops t (firstBarrier p+7) extra _ s _ (a_exit_jump_site p) hp
    (execute_jump ops p t (firstBarrier p+12) s)

theorem a_round_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aRoundState p ops input tile t e zero s).trace.length=s.trace.length+(if zero then 1 else 2) := by
  cases zero <;> simp [aRoundState,aBodyState,aStored,aZeroStored,written,aLoaded,setIndex,advance,record,Nat.add_assoc]

theorem a_loop_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e n : Nat) (zero : Bool) (s : State α) :
    (aLoopState p ops input tile t zero e n s).trace.length=s.trace.length+n*(if zero then 1 else 2) := by
  induction n generalizing e s with
  | zero => simp [aLoopState]
  | succ n ih =>
    rw [aLoopState,ih,a_round_trace_length]
    simp only [Nat.succ_mul]
    omega

#print axioms a_loop_indices
#print axioms a_loop_reads
#print axioms a_loop_pc
#print axioms a_loop_frames
#print axioms a_loop_eq
#print axioms a_loop_exit_eq
#print axioms a_exit_jump_site
#print axioms a_exit_jump_eq
#print axioms a_round_trace_length
#print axioms a_loop_trace_length
end LarkNativeAwqGemm
