import Lark.NativeSoftmaxNormRounds

/-! Complete actual normalization lane: shared-total read, seven rounds, false
outer exit and arrival at the source's own halt instruction. Both full sources
run under the original lane fuel. The repaired trace has the Good property;
the original's unused clamped reads are deliberately not classified as Good. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normExit (guarded : Bool) (t : Nat) (s : State α) : State α := advance s t (normPc guarded 115)

theorem norm_exit_eq (p : Shape) (guarded : Bool) (ops : Ops α) (t tid extra : Nat) (s : State α)
    (hp : s.pc t=95) (h17 : s.indices t 17=some ((base tid 7 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+1) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normExit guarded t s) := by
  have hb : 50257≤base tid 7 := by unfold base; omega
  have pred := predicate_nlt_of (geometry p) t s (.ivar 17) (.const 50257) (base tid 7 : Int) 50257 h17 rfl (by omega)
  have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 17) (.const 50257)) (normPc guarded 115)) s=
      some (normExit guarded t s) := by simp [execute,pred,hp,normExit]
  exact scalar_step p guarded ops t 95 extra _ s _ (norm_outer_codes guarded).1 hp e

theorem norm_exit_fields (guarded : Bool) (t : Nat) (s : State α) :
    (normExit guarded t s).pc t=normPc guarded 115 ∧ (normExit guarded t s).memory=s.memory ∧
    (normExit guarded t s).indices=s.indices ∧ (normExit guarded t s).regs=s.regs ∧
    (normExit guarded t s).epochs=s.epochs ∧ (normExit guarded t s).trace=s.trace := by simp [normExit,advance]

def normPassState (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) : State α :=
  normRounds guarded ops input row tid 0 7 (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s)

def normLaneState (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) : State α :=
  normExit guarded (row*1024+tid) (normPassState guarded ops input row tid s)

def normLaneCost (guarded : Bool) (tid : Nat) : Nat := 2+normRoundsCost guarded tid 0 7+1

theorem norm_pass_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    NormRoundReady p ops input row tid 7 (normPassState guarded ops input row tid s) :=
  norm_rounds_ready p guarded ops input row tid 0 7 _ (by decide) (norm_start_ready p ops input row tid s entry)

theorem norm_lane_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid extra : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) (extra+normLaneCost guarded tid) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normLaneState guarded ops input row tid s) := by
  have ht := entry.bound
  have started := norm_start_ready p ops input row tid s entry
  have last := norm_pass_ready p guarded ops input row tid s entry
  have tidIndex : s.indices (row*1024+tid) 1=some (tid : Int) := by
    simpa only [show (row*1024+tid)%1024=tid by omega] using entry.native.2.1
  have total : s.memory (sumPartialCell (row*1024+tid) 0)=some (rowExpSum ops input row) := by
    simpa only [sumPartialCell,show (row*1024+tid)/1024=row by omega] using entry.total
  rewrite [show extra+normLaneCost guarded tid=((extra+1)+normRoundsCost guarded tid 0 7)+2 by
    unfold normLaneCost; omega,
    norm_start_eq p guarded ops _ (row*1024+tid) tid _ s ht entry.pc tidIndex total,
    norm_rounds_eq p guarded ops input row tid 0 7 (extra+1) _ (by decide) started]
  exact norm_exit_eq p guarded ops (row*1024+tid) tid extra _ last.pc last.base

theorem norm_lane_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α) :
    (normLaneState guarded ops input row tid s).pc (row*1024+tid)=normPc guarded 115 :=
  (norm_exit_fields guarded (row*1024+tid) _).1

theorem norm_lane_cost_bound (guarded : Bool) (tid : Nat) : normLaneCost guarded tid≤948 := by
  have h := norm_rounds_cost_bound guarded tid 0 7
  unfold normLaneCost
  omega

theorem norm_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane s=
      some (normLaneState guarded ops input row tid s) := by
  have hc := norm_lane_cost_bound guarded tid
  let extra := 4096-normLaneCost guarded tid
  have positive : 0<extra := by dsimp only [extra]; omega
  have total : fuel.lane=extra+normLaneCost guarded tid := by dsimp only [fuel,extra]; omega
  have parked : LarkCollective.parked (program guarded) (normLaneState guarded ops input row tid s) (row*1024+tid)=some .halt := by
    simp only [LarkCollective.parked,norm_lane_pc,norm_round_end_codes guarded |>.2.2]
  rewrite [total,norm_lane_eq p guarded ops input row tid extra s entry]
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : extra ≠ 0)
  rewrite [hn]
  simp only [LarkCollective.runLane,parked]

theorem norm_lane_outputs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) : NormPast ops input row tid 7 (normLaneState guarded ops input row tid s) := by
  intro it hi c hc hcol
  dsimp only [normLaneState,normPassState]
  rewrite [(norm_exit_fields guarded (row*1024+tid) _).2.1]
  exact norm_rounds_past guarded ops input row tid 0 7 _ (by intro it hi; omega) it hi c hc hcol

theorem norm_lane_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) : (normLaneState guarded ops input row tid s).epochs=s.epochs :=
  (norm_exit_fields guarded (row*1024+tid) _).2.2.2.2.1.trans
    ((norm_rounds_epochs guarded ops input row tid 0 7 _).trans
      (norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).2.1)

theorem norm_lane_present (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    NormPresent row (normLaneState guarded ops input row tid s) :=
  norm_present_memory row _ _ (norm_exit_fields guarded (row*1024+tid) _).2.1
    (norm_pass_ready p guarded ops input row tid s entry).present

theorem norm_lane_native (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : NormLaneEntry p ops input row tid s) :
    MaxNativeIndices (row*1024+tid) (normLaneState guarded ops input row tid s) := by
  have hi := (norm_pass_ready p guarded ops input row tid s entry).native
  simpa only [MaxNativeIndices,normLaneState,norm_exit_fields guarded (row*1024+tid) _ |>.2.2.1] using hi

theorem norm_lane_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) :
    (normLaneState guarded ops input row tid s).trace.length=s.trace.length+1+2*normRoundsCount guarded tid 0 7 := by
  dsimp only [normLaneState,normPassState]
  rewrite [(norm_exit_fields guarded (row*1024+tid) _).2.2.2.2.2,norm_rounds_trace_length,
    (norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).2.2]
  simp only [List.length_cons]

theorem norm_lane_fixed_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) (he : (s.epochs (row*1024+tid)).block=4)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normLaneState true ops input row tid s).trace, Good a := by
  intro a ha
  change a ∈ (normExit true (row*1024+tid) _).trace at ha
  rewrite [(norm_exit_fields true (row*1024+tid) _).2.2.2.2.2] at ha
  exact norm_rounds_fixed_good ops input row tid 0 7 _ ht
    (norm_start_good ops (rowExpSum ops input row) (row*1024+tid) tid s he good) a ha

theorem norm_lane_fixed_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) (he : (s.epochs (row*1024+tid)).block=4)
    (good : ∀ a ∈ s.trace, Good a) : raceFree (geometry p) (normLaneState true ops input row tid s).trace=true :=
  race_free p _ (norm_lane_fixed_good ops input row tid s ht he good)

theorem initial_norm_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane
      (sumState p ops input row (initial (layout p) input outside))=
      some (normLaneState guarded ops input row tid (sumState p ops input row (initial (layout p) input outside))) :=
  norm_lane_run p guarded ops input row tid _ (initial_norm_entry p ops input outside row tid hr ht)

#print axioms norm_exit_eq
#print axioms norm_exit_fields
#print axioms norm_pass_ready
#print axioms norm_lane_eq
#print axioms norm_lane_pc
#print axioms norm_lane_cost_bound
#print axioms norm_lane_run
#print axioms norm_lane_outputs
#print axioms norm_lane_epochs
#print axioms norm_lane_present
#print axioms norm_lane_native
#print axioms norm_lane_trace_length
#print axioms norm_lane_fixed_good
#print axioms norm_lane_fixed_race_free
#print axioms initial_norm_lane_run
end LarkNativeSoftmax
