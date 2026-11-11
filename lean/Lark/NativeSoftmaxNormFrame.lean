import Lark.NativeSoftmaxNormCounts

/-! Whole normalization-lane frames for sequential lane and wave composition.
Later lanes retain their own exponential inputs and entry controls, even when
the original source's unused clamped reads observe previously normalized cells. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_start_other (ops : Ops α) (total : α) (t tid u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStart ops total t tid s) := by simp [OtherThread,normStart,setReg,setIndex,record,advance,hu]

theorem norm_exit_other (guarded : Bool) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normExit guarded t s) := by simp [OtherThread,normExit,advance,hu]

theorem norm_pipeline_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid count u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s
      (normExit guarded (row*1024+tid)
        (normRounds guarded ops input row tid 0 count (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s))) :=
  other_thread_trans (row*1024+tid) u _ _ _ (norm_start_other ops _ (row*1024+tid) tid u s hu)
    (other_thread_trans (row*1024+tid) u _ _ _ (norm_rounds_other guarded ops input row tid 0 count u _ hu)
      (norm_exit_other guarded (row*1024+tid) u _ hu))

theorem norm_lane_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normLaneState guarded ops input row tid s) :=
  norm_pipeline_other guarded ops input row tid 7 u s hu

theorem norm_lane_native_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid u : Nat) (s : State α) (hu : u ≠ row*1024+tid) (hi : MaxNativeIndices u s) :
    MaxNativeIndices u (normLaneState guarded ops input row tid s) := by
  have hx := (norm_lane_other guarded ops input row tid u s hu).2.1
  exact ⟨(congrArg (fun ix => ix 0) hx).trans hi.1,(congrArg (fun ix => ix 1) hx).trans hi.2.1,
    (congrArg (fun ix => ix 2) hx).trans hi.2.2.1,(congrArg (fun ix => ix 3) hx).trans hi.2.2.2⟩

theorem norm_lane_memory_frame (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 1)
    (houtput : ∀ it, it<7 → ∀ c, c<8 → column tid it c<50257 → l ≠ globalCell 0 (address row (column tid it c))) :
    (normLaneState guarded ops input row tid s).memory l=s.memory l :=
  (congrFun (norm_exit_fields guarded (row*1024+tid) _).2.1 l).trans
    ((norm_rounds_memory_frame guarded ops input row tid 0 7 _ l hprivate (by
      intro it _ hi c hc hcol; exact houtput it hi c hc hcol)).trans
      (congrFun (norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).1 l))

theorem norm_lane_output_other_thread (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid offset : Nat) (s : State α) (ht : tid<1024) (ho : writer offset ≠ row*1024+tid) :
    (normLaneState guarded ops input row tid s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply norm_lane_memory_frame guarded ops input row tid s (globalCell 0 offset)
    (Or.inl (by change Space.global ≠ Space.local; decide))
  intro it hi c hc hcol he
  have hx := congrArg Location.offset he
  change offset=address row (column tid it c) at hx
  apply ho
  rewrite [hx]
  exact address_writer row tid it c ht hcol

theorem norm_lane_shared_total (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) :
    (normLaneState guarded ops input row tid s).memory ⟨.shared,row,1,0⟩=s.memory ⟨.shared,row,1,0⟩ := by
  apply norm_lane_memory_frame guarded ops input row tid s _
    (Or.inl (by change Space.shared ≠ Space.local; decide))
  intro it hi c hc hcol he
  have hs := congrArg Location.space he
  simp [globalCell] at hs

theorem norm_lane_entry_other (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid other : Nat) (s : State α) (hne : other ≠ tid)
    (entry : NormLaneEntry p ops input row tid s) (next : NormLaneEntry p ops input row other s) :
    NormLaneEntry p ops input row other (normLaneState guarded ops input row tid s) := by
  have hu : row*1024+other ≠ row*1024+tid := by omega
  have hf := norm_lane_other guarded ops input row tid (row*1024+other) s hu
  exact {
    valid := next.valid
    bound := next.bound
    pc := hf.1.trans next.pc
    native := norm_lane_native_other guarded ops input row tid (row*1024+other) s hu next.native
    total := (norm_lane_shared_total guarded ops input row tid s).trans next.total
    epoch := (congrArg (fun epochs => (epochs (row*1024+other)).block)
      (norm_lane_epochs guarded ops input row tid s)).trans next.epoch
    future := by
      intro it hi hib c hc hcol
      rewrite [norm_lane_output_other_thread guarded ops input row tid _ s entry.bound (by
        rewrite [address_writer row other it c next.bound hcol]
        exact hu)]
      exact next.future it hi hib c hc hcol
    present := norm_lane_present p guarded ops input row tid s entry }

#print axioms norm_start_other
#print axioms norm_exit_other
#print axioms norm_pipeline_other
#print axioms norm_lane_other
#print axioms norm_lane_native_other
#print axioms norm_lane_memory_frame
#print axioms norm_lane_output_other_thread
#print axioms norm_lane_shared_total
#print axioms norm_lane_entry_other
end LarkNativeSoftmax
