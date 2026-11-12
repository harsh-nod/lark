import Lark.NativeAwqGemmAStore

/-! One complete iteration of either source A-staging loop: condition,
actual store, signed counter increment and back edge. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def aLoopPC (p : Shape) (zero : Bool) : Nat := if zero then firstBarrier p+8 else firstBarrier p+3
def aExitPC (p : Shape) (zero : Bool) : Nat := if zero then firstBarrier p+12 else firstBarrier p+7

theorem a_loop_test_site (p : Shape) (zero : Bool) : (program p)[aLoopPC p zero]?=
    some (.scalar (.branch (.lt (v 14) (c 8)) (aExitPC p zero))) := by
  cases zero with
  | false =>
    change (program p)[firstBarrier p+3]?=_
    rw [show firstBarrier p+3=16+4*banks p+2 by unfold firstBarrier; omega,staging_site p 2 (by decide)]
    rfl
  | true =>
    change (program p)[firstBarrier p+8]?=_
    rw [show firstBarrier p+8=16+4*banks p+7 by unfold firstBarrier; omega,staging_site p 7 (by decide)]
    rfl

theorem a_increment_site (p : Shape) (zero : Bool) : (program p)[aLoopPC p zero+2]?=
    some (.scalar (.index 14 (.add (v 14) (c 1)))) := by
  cases zero with
  | false =>
    change (program p)[firstBarrier p+5]?=_
    rw [show firstBarrier p+5=16+4*banks p+4 by unfold firstBarrier; omega,staging_site p 4 (by decide)]
    rfl
  | true =>
    change (program p)[firstBarrier p+10]?=_
    rw [show firstBarrier p+10=16+4*banks p+9 by unfold firstBarrier; omega,staging_site p 9 (by decide)]
    rfl

theorem a_jump_site (p : Shape) (zero : Bool) : (program p)[aLoopPC p zero+3]?=
    some (.scalar (.jump (aLoopPC p zero))) := by
  cases zero with
  | false =>
    change (program p)[firstBarrier p+6]?=_
    rw [show firstBarrier p+6=16+4*banks p+5 by unfold firstBarrier; omega,staging_site p 5 (by decide)]
    rfl
  | true =>
    change (program p)[firstBarrier p+11]?=_
    rw [show firstBarrier p+11=16+4*banks p+10 by unfold firstBarrier; omega,staging_site p 10 (by decide)]
    rfl

def aBodyState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) : State α :=
  let entered := advance s t (aLoopPC p zero+1)
  if zero then aZeroStored p ops t e entered else aStored p input tile t e entered

def aRoundState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) : State α :=
  advance (setIndex (aBodyState p ops input tile t e zero s) t 14 ((e+1 : Nat) : Int)
    (aLoopPC p zero+3)) t (aLoopPC p zero)

theorem a_body_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (h : AIndices p tile t e s) :
    AIndices p tile t e (aBodyState p ops input tile t e zero s) := by
  cases zero with
  | false => exact a_stored_indices p input tile t e _ (a_indices_of_indices p tile t e s _ h rfl)
  | true => exact a_zero_stored_indices p ops tile t e _ (a_indices_of_indices p tile t e s _ h rfl)

theorem a_body_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (h : Reads p input s) :
    Reads p input (aBodyState p ops input tile t e zero s) := by
  cases zero with
  | false => exact a_stored_reads p input tile t e _ h
  | true => exact a_zero_stored_reads p ops input t e _ h

theorem a_body_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aBodyState p ops input tile t e zero s).pc t=aLoopPC p zero+2 := by
  cases zero <;> simp [aBodyState,aLoopPC,aStored,aZeroStored,written,advance,Nat.add_assoc]

theorem a_body_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aBodyState p ops input tile t e zero s).indices=s.indices ∧
      (aBodyState p ops input tile t e zero s).regs=s.regs ∧
        (aBodyState p ops input tile t e zero s).epochs=s.epochs := by
  cases zero <;> exact ⟨rfl,rfl,rfl⟩

theorem a_body_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e extra : Nat) (zero : Bool) (s : State α)
    (hk : tile<p.k/32) (he : e<8) (h : AIndices p tile t e s) (reads : Reads p input s)
    (hr : zero=false → inputRow p t<p.m) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1)
      (advance s t (aLoopPC p zero+1))=
        LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aBodyState p ops input tile t e zero s) := by
  cases zero with
  | false =>
    exact a_store_run p ops input tile t e extra _ (hr rfl) hk he
      (a_indices_of_indices p tile t e s _ h rfl) reads (by simp [aLoopPC,advance,Nat.add_assoc])
  | true =>
    exact a_zero_store_run p ops tile t e extra _ he
      (a_indices_of_indices p tile t e s _ h rfl) (by simp [aLoopPC,advance,Nat.add_assoc])

theorem a_round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e extra : Nat) (zero : Bool) (s : State α)
    (hk : tile<p.k/32) (he : e<8) (h : AIndices p tile t e s) (reads : Reads p input s)
    (hr : zero=false → inputRow p t<p.m) (hp : s.pc t=aLoopPC p zero) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aRoundState p ops input tile t e zero s) := by
  let entered := advance s t (aLoopPC p zero+1)
  let body := aBodyState p ops input tile t e zero s
  let incremented := setIndex body t 14 ((e+1 : Nat) : Int) (aLoopPC p zero+3)
  have pred := eval_int_lt_true (geometry p) t s (v 14) (c 8) (e : Int) 8 h.element
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have branchStep : execute ops (layout p) (geometry p) t (.branch (.lt (v 14) (c 8)) (aExitPC p zero)) s=
      some entered := by
    have step := execute_branch_true ops p t (aExitPC p zero) (.lt (v 14) (c 8)) s pred
    rw [hp] at step
    exact step
  have bodyReady : AIndices p tile t e body := a_body_indices p ops input tile t e zero s h
  have bodyPC : body.pc t=aLoopPC p zero+2 := a_body_pc p ops input tile t e zero s
  have incrementStep := execute_index_of ops p t 14 (aLoopPC p zero+3) (.add (v 14) (c 1)) body
    ((e+1 : Nat) : Int) (eval_a_increment p tile t e body he bodyReady) (by omega)
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p ops t (aLoopPC p zero) (extra+3) _ s entered (a_loop_test_site p zero) hp branchStep]
  rewrite [show extra+3=(extra+2)+1 by omega,a_body_run p ops input tile t e (extra+2) zero s hk he h reads hr]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (aLoopPC p zero+2) (extra+1) _ body incremented (a_increment_site p zero) bodyPC incrementStep]
  exact scalar_step p ops t (aLoopPC p zero+3) extra _ incremented _ (a_jump_site p zero)
    (by simp [incremented,setIndex,advance]) (execute_jump ops p t (aLoopPC p zero) incremented)

theorem a_round_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (h : AIndices p tile t e s) :
    AIndices p tile t (e+1) (aRoundState p ops input tile t e zero s) :=
  a_indices_of_indices p tile t (e+1) _ _
    (a_indices_set_element p tile t e (e+1) (aLoopPC p zero+3) _ (a_body_indices p ops input tile t e zero s h)) rfl

theorem a_round_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) (h : Reads p input s) :
    Reads p input (aRoundState p ops input tile t e zero s) := a_body_reads p ops input tile t e zero s h

theorem a_round_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aRoundState p ops input tile t e zero s).pc t=aLoopPC p zero := by simp [aRoundState,advance]

theorem a_round_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t e : Nat) (zero : Bool) (s : State α) :
    (aRoundState p ops input tile t e zero s).regs=s.regs ∧
      (aRoundState p ops input tile t e zero s).epochs=s.epochs :=
  ⟨(a_body_frames p ops input tile t e zero s).2.1,(a_body_frames p ops input tile t e zero s).2.2⟩

#print axioms a_loop_test_site
#print axioms a_increment_site
#print axioms a_jump_site
#print axioms a_body_indices
#print axioms a_body_reads
#print axioms a_body_pc
#print axioms a_body_frames
#print axioms a_body_run
#print axioms a_round_eq
#print axioms a_round_indices
#print axioms a_round_reads
#print axioms a_round_pc
#print axioms a_round_frames
end LarkNativeAwqGemm
