import Lark.NativeAwqGemmBRound

/-! Induction over the eight source B-staging elements of one chunk,
including the final failed element test. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def bLoopState (p : Shape) (input : Nat → Nat → α) (tile t chunk : Nat) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | e,n+1,s => bLoopState p input tile t chunk (e+1) n (bRoundState p input tile t chunk e s)

theorem b_loop_indices (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α)
    (h : BIndices p tile t chunk e s) : BIndices p tile t chunk (e+n) (bLoopState p input tile t chunk e n s) := by
  induction n generalizing e s with
  | zero => exact h
  | succ n ih =>
    have next := ih (e+1) (bRoundState p input tile t chunk e s) (b_round_indices p input tile t chunk e s h)
    simpa only [bLoopState,show (e+1)+n=e+(n+1) by omega] using next

theorem b_loop_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (bLoopState p input tile t chunk e n s) := by
  induction n generalizing e s with
  | zero => exact h
  | succ n ih => exact ih (e+1) _ (b_round_reads p input tile t chunk e s h)

theorem b_loop_pc (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α)
    (hp : s.pc t=bLoopPC p) : (bLoopState p input tile t chunk e n s).pc t=bLoopPC p := by
  induction n generalizing e s with
  | zero => exact hp
  | succ n ih => exact ih (e+1) _ (b_round_pc p input tile t chunk e s)

theorem b_loop_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α) :
    (bLoopState p input tile t chunk e n s).regs=s.regs ∧
      (bLoopState p input tile t chunk e n s).epochs=s.epochs := by
  induction n generalizing e s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have round := b_round_frames p input tile t chunk e s
    have rest := ih (e+1) (bRoundState p input tile t chunk e s)
    exact ⟨rest.1.trans round.1,rest.2.trans round.2⟩

theorem b_loop_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk e n extra : Nat) (s : State α)
    (hk : tile<p.k/32) (hc : chunk<banks p) (hn : e+n≤8) (h : BIndices p tile t chunk e s)
    (reads : Reads p input s) (hp : s.pc t=bLoopPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4*n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bLoopState p input tile t chunk e n s) := by
  induction n generalizing e extra s with
  | zero => rfl
  | succ n ih =>
    rewrite [show extra+4*(n+1)=(extra+4*n)+4 by omega,
      b_round_eq p ops input tile t chunk e (extra+4*n) s hk hc (by omega) h reads hp]
    exact ih (e+1) extra (bRoundState p input tile t chunk e s) (by omega)
      (b_round_indices p input tile t chunk e s h) (b_round_reads p input tile t chunk e s reads)
      (b_round_pc p input tile t chunk e s)

theorem b_loop_exit_eq (p : Shape) (ops : Ops α) (tile t chunk extra : Nat) (s : State α)
    (h : BIndices p tile t chunk 8 s) (hp : s.pc t=bLoopPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (advance s t (bExitPC p)) := by
  have predicate := eval_int_lt_false (geometry p) t s (v 18) (c 8) 8 8 h.element
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  exact scalar_step p ops t (bLoopPC p) extra _ s _ (b_loop_test_site p) hp
    (execute_branch_false ops p t (bExitPC p) (.lt (v 18) (c 8)) s predicate)

theorem b_round_trace_length (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bRoundState p input tile t chunk e s).trace.length=s.trace.length+2 := by
  simp [bRoundState,bBodyState,bStored,written,bLoaded,setIndex,advance,record,Nat.add_assoc]

theorem b_loop_trace_length (p : Shape) (input : Nat → Nat → α) (tile t chunk e n : Nat) (s : State α) :
    (bLoopState p input tile t chunk e n s).trace.length=s.trace.length+2*n := by
  induction n generalizing e s with
  | zero => simp [bLoopState]
  | succ n ih => rw [bLoopState,ih,b_round_trace_length]; omega

#print axioms b_loop_indices
#print axioms b_loop_reads
#print axioms b_loop_pc
#print axioms b_loop_frames
#print axioms b_loop_eq
#print axioms b_loop_exit_eq
#print axioms b_round_trace_length
#print axioms b_loop_trace_length
end LarkNativeAwqGemm
