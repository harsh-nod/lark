import Lark.NativeSoftmaxSumSerialStep

/-! Actual sequential lane fold with a deferred shared-read invariant. Once
the leader has stored its result, later lanes need only their skip controls. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure SumSerialEntry (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α) : Prop where
  pc : ∀ t ∈ ts, s.pc t=83
  native : ∀ t ∈ ts, MaxNativeIndices t s
  pending : row*1024 ∈ ts → SumSerialReads values (row*1024) s
  epoch : ∀ t ∈ ts, (s.epochs t).block=3
  good : ∀ a ∈ s.trace, Good a

def sumSerialLaneFold (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => sumSerialStep ops values row t s) s

theorem sum_serial_entry_tail (ops : Ops α) (values : Nat → α) (row t : Nat) (ts : List Nat)
    (s : State α) (hn : t ∉ ts) (entry : SumSerialEntry values row (t::ts) s) :
    SumSerialEntry values row ts (sumSerialStep ops values row t s) := by
  exact {
    pc := by
      intro u hu
      have he : u ≠ t := by intro h; subst u; exact hn hu
      exact (sum_serial_step_other ops values row t u s he).1.trans (entry.pc u (by simp [hu]))
    native := fun u hu => sum_serial_step_native ops values row t u s (entry.native u (by simp [hu]))
    pending := by
      intro hm slot hs
      have he : t ≠ row*1024 := by intro h; subst t; exact hn hm
      rewrite [sum_serial_step_nonleader_memory ops values row t s he]
      exact entry.pending (by simp [hm]) slot hs
    epoch := by
      intro u hu
      exact (congrArg (fun epochs => (epochs u).block) (sum_serial_step_epochs ops values row t s)).trans
        (entry.epoch u (by simp [hu]))
    good := sum_serial_step_good ops values row t s (entry.epoch t (by simp)) entry.good }

theorem sum_serial_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hb : ∀ t ∈ ts, t/1024=row) (entry : SumSerialEntry values row ts s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s =
      some (sumSerialLaneFold ops values row ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,sum_serial_step_run p guarded ops values row t s (hb t (by simp))
      (entry.pc t (by simp)) (entry.native t (by simp)) (by
        intro h; subst t; exact entry.pending (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (sum_serial_entry_tail ops values row t ts s hnot entry)

theorem sum_serial_fold_other (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (t : Nat) (s : State α) (ht : t ∉ ts) : (sumSerialLaneFold ops values row ts s).pc t=s.pc t := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
    have he : t ≠ u := by intro h; subst t; simp at ht
    have hm : t ∉ ts := by intro h; exact ht (by simp [h])
    exact (ih (sumSerialStep ops values row u s) hm).trans (sum_serial_step_other ops values row u t s he).1

theorem sum_serial_fold_member_pc (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (sumSerialLaneFold ops values row ts s).pc t=92 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ht with he | hm
    · subst t
      exact (sum_serial_fold_other ops values row ts u (sumSerialStep ops values row u s) hnot).trans
        (sum_serial_step_pc ops values row u s)
    · exact ih (sumSerialStep ops values row u s) htail hm

theorem sum_serial_fold_native (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (t : Nat) (s : State α) (hi : MaxNativeIndices t s) :
    MaxNativeIndices t (sumSerialLaneFold ops values row ts s) := by
  induction ts generalizing s with
  | nil => exact hi
  | cons u ts ih => exact ih (sumSerialStep ops values row u s) (sum_serial_step_native ops values row u t s hi)

theorem sum_serial_fold_epochs (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α) :
    (sumSerialLaneFold ops values row ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (sumSerialStep ops values row t s)).trans (sum_serial_step_epochs ops values row t s)

theorem sum_serial_fold_no_leader (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (s : State α) (hn : row*1024 ∉ ts) : (sumSerialLaneFold ops values row ts s).memory=s.memory := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have he : t ≠ row*1024 := by intro h; subst t; simp at hn
    have hm : row*1024 ∉ ts := by intro h; exact hn (by simp [h])
    exact (ih (sumSerialStep ops values row t s) hm).trans (sum_serial_step_nonleader_memory ops values row t s he)

theorem sum_serial_fold_memory_other (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (s : State α) (l : Location) (hl : l ≠ sumPartialCell (row*1024) 0) :
    (sumSerialLaneFold ops values row ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    exact (ih (sumSerialStep ops values row t s)).trans
      (sum_serial_step_memory_other ops values row t s l hl)

theorem sum_serial_step_value (ops : Ops α) (values : Nat → α) (row : Nat) (s : State α) :
    (sumSerialStep ops values row (row*1024) s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  simpa only [sumSerialStep,↓reduceIte] using sum_serial_lane_value ops values (row*1024) s

theorem sum_serial_step_preserves_value (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α)
    (hv : s.memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values)) :
    (sumSerialStep ops values row t s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  by_cases he : t=row*1024
  · subst t; exact sum_serial_step_value ops values row s
  · rewrite [sum_serial_step_nonleader_memory ops values row t s he]
    exact hv

theorem sum_serial_fold_preserves_value (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α)
    (hv : s.memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values)) :
    (sumSerialLaneFold ops values row ts s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  induction ts generalizing s with
  | nil => exact hv
  | cons t ts ih => exact ih (sumSerialStep ops values row t s) (sum_serial_step_preserves_value ops values row t s hv)

theorem sum_serial_fold_value (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α)
    (hm : row*1024 ∈ ts) :
    (sumSerialLaneFold ops values row ts s).memory (sumPartialCell (row*1024) 0)=some (sumSerialTotal ops values) := by
  induction ts generalizing s with
  | nil => simp at hm
  | cons t ts ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst t
      exact sum_serial_fold_preserves_value ops values row ts _ (sum_serial_step_value ops values row s)
    · exact ih (sumSerialStep ops values row t s) hm

theorem sum_serial_step_trace_length (ops : Ops α) (values : Nat → α) (row t : Nat) (s : State α) :
    (sumSerialStep ops values row t s).trace.length=s.trace.length+(if t=row*1024 then 33 else 0) := by
  by_cases he : t=row*1024
  · simpa only [sumSerialStep,if_pos he] using sum_serial_lane_trace_length ops values t s
  · simp [sumSerialStep,he,sumSerialSkip,advance]

def sumLeaderCount (row : Nat) (ts : List Nat) : Nat := ts.countP (fun t => t==row*1024)

theorem sum_serial_fold_trace_length (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat) (s : State α) :
    (sumSerialLaneFold ops values row ts s).trace.length=s.trace.length+33*sumLeaderCount row ts := by
  induction ts generalizing s with
  | nil => simp [sumSerialLaneFold,sumLeaderCount]
  | cons t ts ih =>
    change (sumSerialLaneFold ops values row ts (sumSerialStep ops values row t s)).trace.length = _
    rewrite [ih,sum_serial_step_trace_length]
    simp only [sumLeaderCount,List.countP_cons,beq_iff_eq]
    by_cases he : t=row*1024 <;> simp only [he,↓reduceIte] <;> omega

theorem sum_serial_fold_good (ops : Ops α) (values : Nat → α) (row : Nat) (ts : List Nat)
    (s : State α) (hn : ts.Nodup) (entry : SumSerialEntry values row ts s) :
    ∀ a ∈ (sumSerialLaneFold ops values row ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact entry.good
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (sum_serial_entry_tail ops values row t ts s hnot entry)

#print axioms sum_serial_entry_tail
#print axioms sum_serial_fold_run
#print axioms sum_serial_fold_other
#print axioms sum_serial_fold_member_pc
#print axioms sum_serial_fold_native
#print axioms sum_serial_fold_epochs
#print axioms sum_serial_fold_no_leader
#print axioms sum_serial_fold_memory_other
#print axioms sum_serial_step_value
#print axioms sum_serial_step_preserves_value
#print axioms sum_serial_fold_preserves_value
#print axioms sum_serial_fold_value
#print axioms sum_serial_step_trace_length
#print axioms sum_serial_fold_trace_length
#print axioms sum_serial_fold_good
end LarkNativeSoftmax
