import Lark.NativeAwqGemmBStore

/-! One B-staging iteration follows the actual condition, global read,
shared write, signed element increment and back edge. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def bLoopPC (p : Shape) : Nat := firstBarrier p+17
def bExitPC (p : Shape) : Nat := firstBarrier p+21

theorem b_loop_test_site (p : Shape) : (program p)[bLoopPC p]?=
    some (.scalar (.branch (.lt (v 18) (c 8)) (bExitPC p))) := by
  rw [show bLoopPC p=16+4*banks p+16 by unfold bLoopPC firstBarrier; omega,staging_site p 16 (by decide)]
  rfl

theorem b_increment_site (p : Shape) : (program p)[bLoopPC p+2]?=
    some (.scalar (.index 18 (.add (v 18) (c 1)))) := by
  rw [show bLoopPC p+2=16+4*banks p+18 by unfold bLoopPC firstBarrier; omega,staging_site p 18 (by decide)]
  rfl

theorem b_jump_site (p : Shape) : (program p)[bLoopPC p+3]?=
    some (.scalar (.jump (bLoopPC p))) := by
  rw [show bLoopPC p+3=16+4*banks p+19 by unfold bLoopPC firstBarrier; omega,staging_site p 19 (by decide)]
  rfl

def bBodyState (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) : State α :=
  bStored p input tile t chunk e (advance s t (bLoopPC p+1))

def bRoundState (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) : State α :=
  advance (setIndex (bBodyState p input tile t chunk e s) t 18 ((e+1 : Nat) : Int)
    (bLoopPC p+3)) t (bLoopPC p)

theorem b_body_indices (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : BIndices p tile t chunk e s) : BIndices p tile t chunk e (bBodyState p input tile t chunk e s) :=
  b_stored_indices p input tile t chunk e _ (b_indices_of_indices p tile t chunk e s _ h rfl)

theorem b_body_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (bBodyState p input tile t chunk e s) :=
  b_stored_reads p input tile t chunk e _ h

theorem b_body_pc (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bBodyState p input tile t chunk e s).pc t=bLoopPC p+2 := by
  simp [bBodyState,bLoopPC,bStored,written,advance,Nat.add_assoc]

theorem b_body_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bBodyState p input tile t chunk e s).indices=s.indices ∧
      (bBodyState p input tile t chunk e s).regs=s.regs ∧
        (bBodyState p input tile t chunk e s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem b_round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t chunk e extra : Nat) (s : State α)
    (hk : tile<p.k/32) (hc : chunk<banks p) (he : e<8) (h : BIndices p tile t chunk e s)
    (reads : Reads p input s) (hp : s.pc t=bLoopPC p) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+4) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bRoundState p input tile t chunk e s) := by
  let entered := advance s t (bLoopPC p+1)
  let body := bBodyState p input tile t chunk e s
  let incremented := setIndex body t 18 ((e+1 : Nat) : Int) (bLoopPC p+3)
  have pred := eval_int_lt_true (geometry p) t s (v 18) (c 8) (e : Int) 8 h.element
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have branchStep : execute ops (layout p) (geometry p) t (.branch (.lt (v 18) (c 8)) (bExitPC p)) s=
      some entered := by
    have step := execute_branch_true ops p t (bExitPC p) (.lt (v 18) (c 8)) s pred
    rw [hp] at step
    exact step
  have bodyReady := b_body_indices p input tile t chunk e s h
  have bodyPC : body.pc t=bLoopPC p+2 := b_body_pc p input tile t chunk e s
  have incrementStep := execute_index_of ops p t 18 (bLoopPC p+3) (.add (v 18) (c 1)) body
    ((e+1 : Nat) : Int) (eval_b_increment p tile t chunk e body he bodyReady) (by omega)
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p ops t (bLoopPC p) (extra+3) _ s entered (b_loop_test_site p) hp branchStep]
  rewrite [show extra+3=(extra+2)+1 by omega,
    b_store_run p ops input tile t chunk e (extra+2) entered hk hc he
      (b_indices_of_indices p tile t chunk e s entered h rfl) reads
      (by simp [entered,bLoopPC,advance,Nat.add_assoc])]
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+2) body=_
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (bLoopPC p+2) (extra+1) _ body incremented (b_increment_site p) bodyPC incrementStep]
  exact scalar_step p ops t (bLoopPC p+3) extra _ incremented _ (b_jump_site p)
    (by simp [incremented,setIndex,advance]) (execute_jump ops p t (bLoopPC p) incremented)

theorem b_round_indices (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : BIndices p tile t chunk e s) : BIndices p tile t chunk (e+1) (bRoundState p input tile t chunk e s) :=
  b_indices_of_indices p tile t chunk (e+1) _ _
    (b_indices_set_element p tile t chunk e (e+1) (bLoopPC p+3) _ (b_body_indices p input tile t chunk e s h)) rfl

theorem b_round_reads (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α)
    (h : Reads p input s) : Reads p input (bRoundState p input tile t chunk e s) :=
  b_body_reads p input tile t chunk e s h

theorem b_round_pc (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bRoundState p input tile t chunk e s).pc t=bLoopPC p := by simp [bRoundState,advance]

theorem b_round_frames (p : Shape) (input : Nat → Nat → α) (tile t chunk e : Nat) (s : State α) :
    (bRoundState p input tile t chunk e s).regs=s.regs ∧
      (bRoundState p input tile t chunk e s).epochs=s.epochs :=
  ⟨(b_body_frames p input tile t chunk e s).2.1,(b_body_frames p input tile t chunk e s).2.2⟩

#print axioms b_loop_test_site
#print axioms b_increment_site
#print axioms b_jump_site
#print axioms b_body_indices
#print axioms b_body_reads
#print axioms b_body_pc
#print axioms b_body_frames
#print axioms b_round_eq
#print axioms b_round_indices
#print axioms b_round_reads
#print axioms b_round_pc
#print axioms b_round_frames
end LarkNativeAwqGemm
