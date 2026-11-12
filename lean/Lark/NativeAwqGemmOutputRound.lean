import Lark.NativeAwqGemmOutputStore

/-! Each original output row guard either executes the converted store or
skips it. Invalid rows do not evaluate an output address or add a trace event. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def outputCost (p : Shape) (t q : Nat) : Nat :=
  if globalOutputRow p t (q%4)<p.m then 2 else 1

def outputRound (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α) : State α :=
  if globalOutputRow p t (q%4)<p.m then
    outputStored p ops t q (values q) (advance s t (outPC p q+1))
  else advance s t (outPC p (q+1))

theorem output_round_pc (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α) :
    (outputRound p ops t q values s).pc t=outPC p (q+1) := by
  unfold outputRound
  split <;> simp [outputStored,written,advance]

theorem output_round_frames (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α) :
    (outputRound p ops t q values s).indices=s.indices ∧
      (outputRound p ops t q values s).regs=s.regs ∧
      (outputRound p ops t q values s).epochs=s.epochs := by
  unfold outputRound
  split <;> exact ⟨rfl,rfl,rfl⟩

theorem output_round_other_pc (p : Shape) (ops : Ops α) (t q u : Nat) (values : Nat → α)
    (s : State α) (hu : u≠t) : (outputRound p ops t q values s).pc u=s.pc u := by
  unfold outputRound
  split <;> simp [outputStored,written,advance,record,hu]

theorem output_round_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t q : Nat) (values : Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputRound p ops t q values s) := by
  unfold outputRound
  split
  · exact output_stored_reads p ops input t q (values q) _ reads
  · exact reads

theorem output_round_trace (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α) :
    (outputRound p ops t q values s).trace=
      if globalOutputRow p t (q%4)<p.m then ⟨t,outCell p t q,true,s.epochs t⟩::s.trace else s.trace := by
  unfold outputRound
  split <;> rfl

theorem output_round_other_memory (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α)
    (s : State α) (loc : Location) (hl : loc≠outCell p t q) :
    (outputRound p ops t q values s).memory loc=s.memory loc := by
  unfold outputRound
  split
  · exact output_stored_other p ops t q (values q) _ loc hl
  · rfl

theorem output_round_value (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α)
    (guard : globalOutputRow p t (q%4)<p.m) :
    (outputRound p ops t q values s).memory (outCell p t q)=some (ops.toHalf (values q)) := by
  rw [outputRound,if_pos guard]
  exact output_stored_value p ops t q (values q) _

theorem output_round_eq (p : Shape) (ops : Ops α) (t q extra : Nat) (values : Nat → α) (s : State α)
    (hq : q<4*banks p) (setup : SetupIndices p t s)
    (hr : s.regs t q=some (values q)) (hp : s.pc t=outPC p q) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+outputCost p t q) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (outputRound p ops t q values s) := by
  have mBound : p.m<2147483648 := by have h := (scalar_parameter_bounds p).1; omega
  have row := setup.outputRows (q%4) (Nat.mod_lt _ (by decide))
  by_cases guard : globalOutputRow p t (q%4)<p.m
  · have pred := eval_int_lt_true (geometry p) t s (v (9+q%4)) (c p.m)
      ((globalOutputRow p t (q%4) : Nat) : Int) (p.m : Int) row
      (eval_nat_const _ _ _ _ mBound) (by omega)
    have branchStep := execute_branch_true ops p t (outPC p (q+1)) (.lt (v (9+q%4)) (c p.m)) s pred
    rw [hp] at branchStep
    rw [outputCost,if_pos guard,show extra+2=(extra+1)+1 by omega,
      scalar_step p ops t (outPC p q) (extra+1) _ s (advance s t (outPC p q+1))
        (output_guard_site p q hq) hp branchStep]
    rw [outputRound,if_pos guard]
    exact output_store_run p ops t q extra (values q) _ hq
      (setup_of_indices p t s _ setup rfl) guard hr (by simp [advance])
  · have pred := eval_int_lt_false (geometry p) t s (v (9+q%4)) (c p.m)
      ((globalOutputRow p t (q%4) : Nat) : Int) (p.m : Int) row
      (eval_nat_const _ _ _ _ mBound) (by omega)
    rw [outputCost,if_neg guard,outputRound,if_neg guard]
    exact scalar_step p ops t (outPC p q) extra _ s _ (output_guard_site p q hq) hp
      (execute_branch_false ops p t (outPC p (q+1)) (.lt (v (9+q%4)) (c p.m)) s pred)

#print axioms output_round_pc
#print axioms output_round_frames
#print axioms output_round_other_pc
#print axioms output_round_reads
#print axioms output_round_trace
#print axioms output_round_other_memory
#print axioms output_round_value
#print axioms output_round_eq
end LarkNativeAwqGemm
