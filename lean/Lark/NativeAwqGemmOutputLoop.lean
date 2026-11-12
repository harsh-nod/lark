import Lark.NativeAwqGemmOutputRound

/-! Induction over all original guarded output pairs, with exact scalar
instruction cost and the actual converted values and write trace. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputRound outputStored

def outputLoop (p : Shape) (ops : Ops α) (t : Nat) (values : Nat → α) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | q,n+1,s => outputLoop p ops t values (q+1) n (outputRound p ops t q values s)

def outputSteps (p : Shape) (t : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | q,n+1 => outputCost p t q+outputSteps p t (q+1) n

def outputEvents (p : Shape) (t : Nat) (epoch : Epoch) : Nat → Nat → List Access
  | _,0 => []
  | q,n+1 => outputEvents p t epoch (q+1) n ++
      (if globalOutputRow p t (q%4)<p.m then [⟨t,outCell p t q,true,epoch⟩] else [])

theorem output_steps_bound (p : Shape) (t q n : Nat) : outputSteps p t q n≤2*n := by
  induction n generalizing q with
  | zero => simp [outputSteps]
  | succ n ih =>
    have step : outputCost p t q≤2 := by unfold outputCost; split <;> omega
    rw [outputSteps]
    have rest := ih (q+1)
    omega

theorem output_loop_frames (p : Shape) (ops : Ops α) (t q n : Nat) (values : Nat → α) (s : State α) :
    (outputLoop p ops t values q n s).indices=s.indices ∧
      (outputLoop p ops t values q n s).regs=s.regs ∧
      (outputLoop p ops t values q n s).epochs=s.epochs := by
  induction n generalizing q s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    have one := output_round_frames p ops t q values s
    have rest := ih (q+1) (outputRound p ops t q values s)
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem output_loop_pc (p : Shape) (ops : Ops α) (t q n : Nat) (values : Nat → α) (s : State α)
    (hp : s.pc t=outPC p q) : (outputLoop p ops t values q n s).pc t=outPC p (q+n) := by
  induction n generalizing q s with
  | zero => exact hp
  | succ n ih =>
    have rest := ih (q+1) (outputRound p ops t q values s) (output_round_pc p ops t q values s)
    simpa only [outputLoop,show (q+1)+n=q+(n+1) by omega] using rest

theorem output_loop_other_pc (p : Shape) (ops : Ops α) (t q n u : Nat) (values : Nat → α)
    (s : State α) (hu : u≠t) : (outputLoop p ops t values q n s).pc u=s.pc u := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    exact (ih (q+1) (outputRound p ops t q values s)).trans (output_round_other_pc p ops t q u values s hu)

theorem output_loop_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t q n : Nat) (values : Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputLoop p ops t values q n s) := by
  induction n generalizing q s with
  | zero => exact reads
  | succ n ih => exact ih (q+1) _ (output_round_reads p ops input t q values s reads)

theorem output_loop_other_memory (p : Shape) (ops : Ops α) (t q n : Nat) (values : Nat → α)
    (s : State α) (loc : Location) (outside : ∀ j, q≤j → j<q+n → loc≠outCell p t j) :
    (outputLoop p ops t values q n s).memory loc=s.memory loc := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    exact (ih (q+1) (outputRound p ops t q values s) (fun j hj hk => outside j (by omega) (by omega))).trans
      (output_round_other_memory p ops t q values s loc (outside q (by omega) (by omega)))

theorem output_loop_value (p : Shape) (ops : Ops α) (t q n r : Nat) (values : Nat → α) (s : State α)
    (hn : q+n≤4*banks p) (hlo : q≤r) (hhi : r<q+n) (guard : globalOutputRow p t (r%4)<p.m) :
    (outputLoop p ops t values q n s).memory (outCell p t r)=some (ops.toHalf (values r)) := by
  induction n generalizing q s with
  | zero => omega
  | succ n ih =>
    rw [outputLoop]
    by_cases same : r=q
    · subst r
      have rest := output_loop_other_memory p ops t (q+1) n values (outputRound p ops t q values s) (outCell p t q)
        (fun j hj hk same => by
          have eq := out_cell_injective p t q j (by omega) (by omega) same
          omega)
      exact rest.trans (output_round_value p ops t q values s guard)
    · exact ih (q+1) (outputRound p ops t q values s) (by omega) (by omega) (by omega)

theorem output_loop_trace (p : Shape) (ops : Ops α) (t q n : Nat) (values : Nat → α) (s : State α) :
    (outputLoop p ops t values q n s).trace=outputEvents p t (s.epochs t) q n ++ s.trace := by
  induction n generalizing q s with
  | zero => rfl
  | succ n ih =>
    rw [outputLoop,ih,(output_round_frames p ops t q values s).2.2,output_round_trace,outputEvents]
    split <;> simp only [List.append_assoc,List.append_nil,List.singleton_append]

theorem output_loop_eq (p : Shape) (ops : Ops α) (t q n extra : Nat) (values : Nat → α) (s : State α)
    (hn : q+n≤4*banks p) (setup : SetupIndices p t s)
    (hr : ∀ j, q≤j → j<q+n → s.regs t j=some (values j)) (hp : s.pc t=outPC p q) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+outputSteps p t q n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (outputLoop p ops t values q n s) := by
  induction n generalizing q extra s with
  | zero => rfl
  | succ n ih =>
    rw [outputSteps,show extra+(outputCost p t q+outputSteps p t (q+1) n)=
      (extra+outputSteps p t (q+1) n)+outputCost p t q by omega,
      output_round_eq p ops t q (extra+outputSteps p t (q+1) n) values s (by omega) setup
        (hr q (by omega) (by omega)) hp]
    apply ih (q+1) extra (outputRound p ops t q values s) (by omega)
      (setup_of_indices p t s _ setup (output_round_frames p ops t q values s).1)
      (fun j hj hk => by rw [(output_round_frames p ops t q values s).2.1]; exact hr j (by omega) (by omega))
      (output_round_pc p ops t q values s)

#print axioms output_steps_bound
#print axioms output_loop_frames
#print axioms output_loop_pc
#print axioms output_loop_other_pc
#print axioms output_loop_reads
#print axioms output_loop_other_memory
#print axioms output_loop_value
#print axioms output_loop_trace
#print axioms output_loop_eq
end LarkNativeAwqGemm
