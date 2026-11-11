import Lark.NativeSoftmaxExpRounds

/-! Actual complete scalar exponentiation/sum prefix, starting after the two
maximum barriers and parking at the first logical32 sum shuffle at PC70.
Both complete source variants retain the original lane fuel. The shuffle,
remaining block phases, whole launch and reference bridge remain open. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setReg execute_pure_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure ExpLaneEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) : Prop where
  valid : row<p.rows
  tidBound : tid<1024
  pc : s.pc (row*1024+tid)=43
  indices : MaxNativeIndices (row*1024+tid) s
  maximum : s.memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row)
  reads : Reads p input s
  epoch : (s.epochs (row*1024+tid)).block=2
  good : ∀ a ∈ s.trace, Good a

theorem exp_lane_entry_of_maximum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    ExpLaneEntry p ops input row tid s :=
  ⟨ready.valid,ht,ready.pc tid ht,ready.indices tid ht,ready.maximum,ready.reads,ready.epoch tid ht,ready.good⟩

def expExit (ops : Ops α) (t : Nat) (s : State α) : State α := setReg (advance s t 69) t 9 (ops.literal 0 1) 70

theorem exp_exit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t tid extra : Nat) (s : State α)
    (hp : s.pc t=46) (h9 : s.indices t 9=some ((base tid 7 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expExit ops t s) := by
  have hb : 50257≤base tid 7 := by unfold base; omega
  have pred := predicate_nlt_of (geometry p) t s (.ivar 9) (.const 50257) (base tid 7 : Int) 50257 h9 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 50257)) 69) s=
      some (advance s t 69) := by simp [execute,pred,hp]
  have e2 := execute_pure_of ops (layout p) (geometry p) t 9 70 (.lit 0 1) (advance s t 69) (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 46 _ _ s _ (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 69 extra _ _ _ (by cases guarded <;> rfl) (by simp [advance]) e2

theorem exp_exit_frames (ops : Ops α) (t : Nat) (s : State α) :
    (expExit ops t s).pc t=70 ∧ (expExit ops t s).memory=s.memory ∧
    (expExit ops t s).indices=s.indices ∧ (expExit ops t s).epochs=s.epochs ∧
    (expExit ops t s).trace=s.trace ∧ (expExit ops t s).regs t 6=s.regs t 6 := by
  simp [expExit,setReg,advance]

def expPassState (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) : State α :=
  expRounds ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 (ops.literal 0 1)
    (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s)

def expPrefixState (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) : State α :=
  expExit ops (row*1024+tid) (expPassState ops input row tid s)

def expPrefixCost (tid : Nat) : Nat := 3+expRoundsCost tid 0 7+2

def threadExpSum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) : α :=
  expRoundsFold ops input (rowMaximum ops input row) row tid 0 7 (ops.literal 0 1)

theorem exp_lane_started (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    ExpRoundReady p input row tid 0 (row*1024+tid) (rowMaximum ops input row) (ops.literal 0 1)
      (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) := by
  have ht := entry.tidBound
  apply exp_round_ready_of_entry p ops input _ row tid (row*1024+tid) _ rfl
  apply exp_start_ready p ops input _ row tid (row*1024+tid) s
  · simpa only [show (row*1024+tid)/1024=row by omega] using entry.indices.1
  · simpa only [show (row*1024+tid)%1024=tid by omega] using entry.indices.2.1
  · exact entry.reads
  · exact entry.epoch
  · exact entry.good

theorem exp_pass_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    ExpRoundReady p input row tid 7 (row*1024+tid) (rowMaximum ops input row) (threadExpSum ops input row tid)
      (expPassState ops input row tid s) :=
  exp_rounds_ready p ops input _ row tid (row*1024+tid) 0 7 _ _ entry.tidBound (exp_lane_started p ops input row tid s entry)

theorem exp_prefix_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid extra : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) (extra+expPrefixCost tid) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (expPrefixState ops input row tid s) := by
  have ht := entry.tidBound
  have started := exp_lane_started p ops input row tid s entry
  have last := exp_pass_ready p ops input row tid s entry
  have tidIndex : s.indices (row*1024+tid) 1=some (tid : Int) := by
    simpa only [show (row*1024+tid)%1024=tid by omega] using entry.indices.2.1
  have maximum : s.memory (partialCell (row*1024+tid) 0)=some (rowMaximum ops input row) := by
    simpa only [partialCell,show (row*1024+tid)/1024=row by omega] using entry.maximum
  rewrite [show extra+expPrefixCost tid=((extra+2)+expRoundsCost tid 0 7)+3 by unfold expPrefixCost; omega,
    exp_start_eq p guarded ops _ (row*1024+tid) tid _ s entry.pc tidIndex maximum]
  rewrite [exp_rounds_eq p guarded ops input _ row tid (row*1024+tid) 0 7 (extra+2) _ _ entry.valid entry.tidBound (by decide) started]
  exact exp_exit_eq p guarded ops (row*1024+tid) tid extra _ last.pc last.baseIndex

theorem exp_prefix_pc (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) :
    (expPrefixState ops input row tid s).pc (row*1024+tid)=70 := (exp_exit_frames ops (row*1024+tid) _).1

theorem exp_prefix_cost_bound (tid : Nat) : expPrefixCost tid≤1062 := by
  have h := exp_rounds_cost_bound tid 0 7
  unfold expPrefixCost
  omega

theorem exp_prefix_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane s =
      some (expPrefixState ops input row tid s) := by
  have hc := exp_prefix_cost_bound tid
  let extra := 4096-expPrefixCost tid
  have positive : 0<extra := by dsimp [extra]; omega
  have total : fuel.lane=extra+expPrefixCost tid := by dsimp [fuel,extra]; omega
  have parked : LarkCollective.parked (program guarded) (expPrefixState ops input row tid s) (row*1024+tid)=some .shuffle := by
    simp only [LarkCollective.parked,exp_prefix_pc]
    cases guarded <;> rfl
  rewrite [total,exp_prefix_eq p guarded ops input row tid extra s entry]
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : extra ≠ 0)
  rewrite [hn]
  simp only [LarkCollective.runLane,parked]

theorem exp_prefix_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    (expPrefixState ops input row tid s).regs (row*1024+tid) 6=some (threadExpSum ops input row tid) :=
  (exp_exit_frames ops (row*1024+tid) _).2.2.2.2.2.trans (exp_pass_ready p ops input row tid s entry).accumulator

theorem exp_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    ∀ a ∈ (expPrefixState ops input row tid s).trace, Good a := by
  change ∀ a ∈ (expExit ops (row*1024+tid) _).trace, Good a
  rewrite [(exp_exit_frames ops (row*1024+tid) _).2.2.2.2.1]
  exact (exp_pass_ready p ops input row tid s entry).good

theorem exp_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : ExpLaneEntry p ops input row tid s) :
    raceFree (geometry p) (expPrefixState ops input row tid s).trace=true :=
  race_free p _ (exp_prefix_good p ops input row tid s entry)

theorem exp_past_outputs_memory (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid upto : Nat) (s next : State α) (hm : next.memory=s.memory)
    (past : ExpPastOutputs ops input offset row tid upto s) :
    ExpPastOutputs ops input offset row tid upto next := by
  intro iteration hi component hc hcol
  rewrite [hm]
  exact past iteration hi component hc hcol

theorem exp_prefix_outputs (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    ExpPastOutputs ops input (rowMaximum ops input row) row tid 7 (expPrefixState ops input row tid s) :=
  exp_past_outputs_memory ops input (rowMaximum ops input row) row tid 7
    (expPassState ops input row tid s) (expPrefixState ops input row tid s)
    (exp_exit_frames ops (row*1024+tid) (expPassState ops input row tid s)).2.1
    (exp_rounds_outputs ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 (ops.literal 0 1)
      (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) ht (by intro iteration hi; omega))

theorem exp_prefix_trace_length (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) :
    (expPrefixState ops input row tid s).trace.length=s.trace.length+113+2*expRoundsCount tid 0 7 := by
  have rounds := exp_rounds_trace_length ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 (ops.literal 0 1)
    (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s)
  have start := exp_start_frames ops (rowMaximum ops input row) (row*1024+tid) tid s
  change (expExit ops (row*1024+tid) _).trace.length=_
  rewrite [(exp_exit_frames ops (row*1024+tid) _).2.2.2.2.1]
  change (expRounds ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 (ops.literal 0 1)
    (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s)).trace.length=_
  rewrite [rounds,start.2.2]
  simp only [List.length_cons]

theorem exp_prefix_epochs (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) :
    (expPrefixState ops input row tid s).epochs=s.epochs :=
  (exp_exit_frames ops (row*1024+tid) _).2.2.2.1.trans
    ((exp_rounds_epochs ops input _ row tid (row*1024+tid) 0 7 _ _).trans
      (exp_start_frames ops (rowMaximum ops input row) (row*1024+tid) tid s).2.1)

theorem exp_prefix_index_other (ops : Ops α) (input : Nat → Nat → α) (row tid r : Nat) (s : State α)
    (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expPrefixState ops input row tid s).indices (row*1024+tid) r=s.indices (row*1024+tid) r :=
  (congrArg (fun indices => indices (row*1024+tid) r) (exp_exit_frames ops (row*1024+tid) _).2.2.1).trans
    ((exp_rounds_index_other ops input _ row tid (row*1024+tid) 0 7 r _ _ h9 h10 h11 h12 h13 h14 h15).trans
      (exp_start_index_other ops (rowMaximum ops input row) (row*1024+tid) tid (row*1024+tid) r s h9))

theorem exp_prefix_native (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α)
    (hi : MaxNativeIndices (row*1024+tid) s) : MaxNativeIndices (row*1024+tid) (expPrefixState ops input row tid s) := by
  exact ⟨(exp_prefix_index_other ops input row tid 0 s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.1,
    (exp_prefix_index_other ops input row tid 1 s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.2.1,
    (exp_prefix_index_other ops input row tid 2 s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.2.2.1,
    (exp_prefix_index_other ops input row tid 3 s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.2.2.2⟩

theorem exp_prefix_memory_frame (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 0)
    (houtput : ∀ iteration, iteration<7 → ∀ component, component<8 → column tid iteration component<50257 →
      l ≠ globalCell 0 (address row (column tid iteration component))) :
    (expPrefixState ops input row tid s).memory l=s.memory l :=
  (congrArg (fun memory => memory l)
    (exp_exit_frames ops (row*1024+tid) (expPassState ops input row tid s)).2.1).trans
    ((exp_rounds_memory_frame ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 (ops.literal 0 1)
      (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) l hprivate
      (by intro iteration _ hi component hc hcol; exact houtput iteration hi component hc hcol)).trans
      (congrArg (fun memory => memory l) (exp_start_frames ops (rowMaximum ops input row) (row*1024+tid) tid s).1))

theorem initial_exp_prefix_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane
        (maximumState p ops input row (initial (layout p) input outside)) =
      some (expPrefixState ops input row tid (maximumState p ops input row (initial (layout p) input outside))) :=
  exp_prefix_run p guarded ops input row tid _
    (exp_lane_entry_of_maximum p ops input row tid _ (initial_maximum_ready p ops input outside row hr) ht)

theorem initial_exp_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    raceFree (geometry p)
      (expPrefixState ops input row tid (maximumState p ops input row (initial (layout p) input outside))).trace=true :=
  exp_prefix_race_free p ops input row tid _
    (exp_lane_entry_of_maximum p ops input row tid _ (initial_maximum_ready p ops input outside row hr) ht)

#print axioms exp_lane_entry_of_maximum
#print axioms exp_exit_eq
#print axioms exp_exit_frames
#print axioms exp_lane_started
#print axioms exp_pass_ready
#print axioms exp_prefix_eq
#print axioms exp_prefix_pc
#print axioms exp_prefix_cost_bound
#print axioms exp_prefix_run
#print axioms exp_prefix_sum
#print axioms exp_prefix_good
#print axioms exp_prefix_race_free
#print axioms exp_past_outputs_memory
#print axioms exp_prefix_outputs
#print axioms exp_prefix_trace_length
#print axioms exp_prefix_epochs
#print axioms exp_prefix_index_other
#print axioms exp_prefix_native
#print axioms exp_prefix_memory_frame
#print axioms initial_exp_prefix_run
#print axioms initial_exp_prefix_race_free
end LarkNativeSoftmax
