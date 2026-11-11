import Lark.NativeSoftmaxMaxRounds

/-! Full actual scalar maximum prefix of both source variants. All seven
outer iterations, their eight-component loops and both false exits execute
before parking at the first logical32 shuffle, with the original lane fuel.
This is a lane-prefix theorem, not whole-kernel softmax correctness. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setReg predicate_nlt_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def maxExit (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setReg (advance s t 19) t 2 (ops.literal 0 1) 20

theorem max_exit_preserves (ops : Ops α) (t : Nat) (s : State α) :
    (maxExit ops t s).memory = s.memory ∧ (maxExit ops t s).epochs = s.epochs ∧
    (maxExit ops t s).trace = s.trace ∧ (maxExit ops t s).regs t 0 = s.regs t 0 := by
  simp [maxExit,setReg,advance]

theorem max_exit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t tid extra : Nat) (s : State α)
    (hp : s.pc t = 6) (h4 : s.indices t 4 = some ((base tid 7 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (maxExit ops t s) := by
  have hb : 50257 ≤ base tid 7 := by unfold base; omega
  have pred := predicate_nlt_of (geometry p) t s (.ivar 4) (.const 50257)
    (base tid 7 : Int) 50257 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 4) (.const 50257)) 19) s = some (advance s t 19) := by
    simp [execute,pred,hp]
  have e2 := execute_pure_of ops (layout p) (geometry p) t 2 20 (.lit 0 1)
    (advance s t 19) (ops.literal 0 1) (by simp [evalExpr]) (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 6 _ _ s _ (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 19 _ _ _ _ (by cases guarded <;> decide)
    (by simp [advance]) e2]
  rfl

def maxPassState (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  maxRounds ops input (t/1024) (t%1024) t 0 7 (ops.literal (-1) 4294967296) (initialized ops t s)

def maxPrefixState (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  maxExit ops t (maxPassState ops input t s)

def maxPrefixCost (tid : Nat) : Nat := 6 + maxRoundsCost tid 0 7 + 2

def threadMaximum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) : α :=
  maxRoundsFold ops input row tid 0 7 (ops.literal (-1) 4294967296)

theorem max_initialized_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    MaxRoundReady p input (t/1024) (t%1024) 0 t (ops.literal (-1) 4294967296) (initialized ops t s) := by
  obtain ⟨hp,h0,h1,_,_,h4,ha⟩ := initialized_fields ops t s
  exact {
    pc := hp, rowIndex := h0, tidIndex := h1
    baseIndex := by simpa only [base,Nat.zero_mul,Nat.add_zero] using h4
    accumulator := ha, reads := reads, good := good }

theorem max_pass_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    MaxRoundReady p input (t/1024) (t%1024) 7 t
      (threadMaximum ops input (t/1024) (t%1024)) (maxPassState ops input t s) :=
  max_rounds_ready p ops input (t/1024) (t%1024) t 0 7 _ _
    (max_initialized_ready p ops input t s reads good)

theorem max_prefix_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra + maxPrefixCost (t%1024)) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxPrefixState ops input t s) := by
  have hr : t/1024 < p.rows := by omega
  have htid : t%1024 < 1024 := Nat.mod_lt _ (by decide)
  have beginReady := max_initialized_ready p ops input t s reads good
  have last := max_pass_ready p ops input t s reads good
  rewrite [show extra + maxPrefixCost (t%1024) =
      (extra + 2 + maxRoundsCost (t%1024) 0 7) + 6 by unfold maxPrefixCost; omega,
    initialized_eq p guarded ops t _ s ht hp]
  rewrite [max_rounds_eq p guarded ops input (t/1024) (t%1024) t 0 7 (extra+2) _ _
    hr htid (by decide) beginReady]
  exact max_exit_eq p guarded ops t (t%1024) extra _ last.pc last.baseIndex

theorem max_prefix_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (maxPrefixState ops input t s).pc t = 20 := by simp [maxPrefixState,maxExit,setReg,advance]

theorem max_prefix_cost_bound (tid : Nat) : maxPrefixCost tid ≤ 547 := by
  have h := max_rounds_cost_bound tid 0 7
  unfold maxPrefixCost
  omega

theorem max_prefix_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (maxPrefixState ops input t s) := by
  have hc := max_prefix_cost_bound (t%1024)
  let extra := 4096 - maxPrefixCost (t%1024)
  have positive : 0 < extra := by dsimp [extra]; omega
  have total : fuel.lane = extra + maxPrefixCost (t%1024) := by dsimp [fuel,extra]; omega
  have parked : LarkCollective.parked (program guarded) (maxPrefixState ops input t s) t = some .shuffle := by
    simp only [LarkCollective.parked,max_prefix_pc]
    cases guarded <;> rfl
  rewrite [total,max_prefix_eq p guarded ops input t extra s ht hp reads good]
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : extra ≠ 0)
  rewrite [hn]
  simp only [LarkCollective.runLane,parked]

theorem max_prefix_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    (maxPrefixState ops input t s).regs t 0 = some (threadMaximum ops input (t/1024) (t%1024)) := by
  unfold maxPrefixState
  rewrite [(max_exit_preserves ops t (maxPassState ops input t s)).2.2.2]
  exact (max_pass_ready p ops input t s reads good).accumulator

theorem max_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (maxPrefixState ops input t s).trace, Good a := by
  unfold maxPrefixState
  rewrite [(max_exit_preserves ops t (maxPassState ops input t s)).2.2.1]
  exact (max_pass_ready p ops input t s reads good).good

theorem max_prefix_frames (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (maxPrefixState ops input t s).memory = s.memory ∧
    (maxPrefixState ops input t s).epochs = s.epochs ∧
    (maxPrefixState ops input t s).trace.length = s.trace.length + 56 := by
  have frame := max_rounds_frames ops input (t/1024) (t%1024) t 0 7
    (ops.literal (-1) 4294967296) (initialized ops t s)
  have init := initialized_preserves ops t s
  have exit := max_exit_preserves ops t (maxPassState ops input t s)
  refine ⟨exit.1.trans (frame.1.trans init.1),exit.2.1.trans (frame.2.1.trans init.2.2),?_⟩
  unfold maxPrefixState
  rewrite [exit.2.2.1]
  change (maxRounds ops input (t/1024) (t%1024) t 0 7 _ _).trace.length = _
  rewrite [frame.2.2,init.2.1]
  rfl

theorem initial_max_prefix_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane
        (initial (layout p) input outside) =
      some (maxPrefixState ops input t (initial (layout p) input outside)) :=
  max_prefix_run p guarded ops input t _ ht rfl (initial_reads p input outside) (by intro a ha; cases ha)

theorem initial_max_prefix_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (maxPrefixState ops input t (initial (layout p) input outside)).regs t 0 =
      some (threadMaximum ops input (t/1024) (t%1024)) :=
  max_prefix_value p ops input t _ (initial_reads p input outside) (by intro a ha; cases ha)

theorem initial_max_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    raceFree (geometry p) (maxPrefixState ops input t (initial (layout p) input outside)).trace = true :=
  race_free p _ (max_prefix_good p ops input t _ (initial_reads p input outside) (by intro a ha; cases ha))

theorem initial_max_prefix_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (maxPrefixState ops input t (initial (layout p) input outside)).trace.length = 56 :=
  (max_prefix_frames ops input t (initial (layout p) input outside)).2.2

#print axioms max_exit_preserves
#print axioms max_exit_eq
#print axioms max_initialized_ready
#print axioms max_pass_ready
#print axioms max_prefix_eq
#print axioms max_prefix_pc
#print axioms max_prefix_cost_bound
#print axioms max_prefix_run
#print axioms max_prefix_value
#print axioms max_prefix_good
#print axioms max_prefix_frames
#print axioms initial_max_prefix_run
#print axioms initial_max_prefix_value
#print axioms initial_max_prefix_race_free
#print axioms initial_max_prefix_trace_length
end LarkNativeSoftmax
