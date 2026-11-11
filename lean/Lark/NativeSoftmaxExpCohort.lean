import Lark.NativeSoftmaxExpFrame

/-! Actual sequential scalar lane fold of an exponentiation cohort. Pending
lanes retain PC43, native indices, input, shared maximum and epoch2 while earlier
lanes execute. Every member then parks at PC70. Collective shuffles are separate. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure ExpCohortEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) : Prop where
  valid : row<p.rows
  pc : ∀ t ∈ ts, s.pc t=43
  native : ∀ t ∈ ts, MaxNativeIndices t s
  maximum : s.memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row)
  reads : Reads p input s
  epoch : ∀ t ∈ ts, (s.epochs t).block=2
  good : ∀ a ∈ s.trace, Good a

def expLaneStep (ops : Ops α) (input : Nat → Nat → α) (row t : Nat) (s : State α) : State α :=
  expPrefixState ops input row (t%1024) s

theorem exp_lane_entry_of_cohort (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (entry : ExpCohortEntry p ops input row ts s)
    (t : Nat) (ht : t ∈ ts) (hb : t/1024=row) : ExpLaneEntry p ops input row (t%1024) s := by
  have he : row*1024+t%1024=t := by omega
  exact {
    valid := entry.valid
    tidBound := Nat.mod_lt _ (by decide)
    pc := by rewrite [he]; exact entry.pc t ht
    indices := by rewrite [he]; exact entry.native t ht
    maximum := entry.maximum
    reads := entry.reads
    epoch := by rewrite [he]; exact entry.epoch t ht
    good := entry.good }

theorem exp_lane_step_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (entry : ExpCohortEntry p ops input row ts s)
    (t : Nat) (ht : t ∈ ts) (hb : t/1024=row) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s=
      some (expLaneStep ops input row t s) := by
  have h := exp_prefix_run p guarded ops input row (t%1024) s (exp_lane_entry_of_cohort p ops input row ts s entry t ht hb)
  simpa only [show row*1024+t%1024=t by omega] using h

theorem exp_lane_step_other (ops : Ops α) (input : Nat → Nat → α)
    (row t u : Nat) (s : State α) (hb : t/1024=row) (hu : u ≠ t) :
    OtherThread t u s (expLaneStep ops input row t s) :=
  exp_prefix_other ops input row (t%1024) u s (by simpa only [show row*1024+t%1024=t by omega] using hu)

theorem exp_cohort_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (ts : List Nat) (s : State α) (hn : t ∉ ts) (hb : t/1024=row)
    (entry : ExpCohortEntry p ops input row (t::ts) s) :
    ExpCohortEntry p ops input row ts (expLaneStep ops input row t s) := by
  have head := exp_lane_entry_of_cohort p ops input row (t::ts) s entry t (by simp) hb
  have he : row*1024+t%1024=t := by omega
  exact {
    valid := entry.valid
    pc := by
      intro u hu
      have hne : u ≠ t := by intro h; subst u; exact hn hu
      exact (exp_lane_step_other ops input row t u s hb hne).1.trans (entry.pc u (by simp [hu]))
    native := by
      intro u hu
      have hne : u ≠ t := by intro h; subst u; exact hn hu
      apply exp_prefix_native_other ops input row (t%1024) u s (by simpa only [he] using hne)
      exact entry.native u (by simp [hu])
    maximum := exp_prefix_shared_maximum ops input row (t%1024) s entry.maximum
    reads := exp_prefix_reads p ops input row (t%1024) s entry.reads
    epoch := by
      intro u hu
      exact (congrArg (fun epochs => (epochs u).block) (exp_prefix_epochs ops input row (t%1024) s)).trans
        (entry.epoch u (by simp [hu]))
    good := exp_prefix_good p ops input row (t%1024) s head }

def expScalarFold (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => expLaneStep ops input row t s) s

theorem exp_scalar_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hb : ∀ t ∈ ts, t/1024=row) (entry : ExpCohortEntry p ops input row ts s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s=
      some (expScalarFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,exp_lane_step_run p guarded ops input row (t::ts) s entry t (by simp) (hb t (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (exp_cohort_entry_tail p ops input row t ts s hnot (hb t (by simp)) entry)

theorem exp_scalar_fold_other (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hu : u ∉ ts) (hb : ∀ t ∈ ts, t/1024=row) :
    OtherThread u u s (expScalarFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have hne : u ≠ t := by intro h; subst u; simp at hu
    have htail : u ∉ ts := by intro h; exact hu (by simp [h])
    exact other_thread_trans u u _ _ _ (exp_lane_step_other ops input row t u s (hb t (by simp)) hne)
      (ih (expLaneStep ops input row t s) htail (by intro t ht; exact hb t (by simp [ht])))

theorem exp_scalar_fold_member_pc (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (t : Nat) (ht : t ∈ ts) : (expScalarFold ops input row ts s).pc t=70 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hrow := hb u (by simp)
    have hrows : ∀ t ∈ ts, t/1024=row := by intro t ht; exact hb t (by simp [ht])
    rcases List.mem_cons.mp ht with he | hm
    · subst t
      exact (exp_scalar_fold_other ops input row ts u (expLaneStep ops input row u s) hnot hrows).1.trans
        (by simpa only [show row*1024+u%1024=u by omega] using exp_prefix_pc ops input row (u%1024) s)
    · exact ih _ htail hrows hm

theorem exp_scalar_fold_member_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (entry : ExpCohortEntry p ops input row ts s) (t : Nat) (ht : t ∈ ts) :
    (expScalarFold ops input row ts s).regs t 6=some (threadExpSum ops input row (t%1024)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hrow := hb u (by simp)
    have hrows : ∀ t ∈ ts, t/1024=row := by intro t ht; exact hb t (by simp [ht])
    rcases List.mem_cons.mp ht with he | hm
    · subst t
      have frame := congrArg (fun regs => regs 6)
        (exp_scalar_fold_other ops input row ts u (expLaneStep ops input row u s) hnot hrows).2.2
      apply frame.trans
      simpa only [show row*1024+u%1024=u by omega] using
        exp_prefix_sum p ops input row (u%1024) s (exp_lane_entry_of_cohort p ops input row (u::ts) s entry u (by simp) hrow)
    · exact ih _ htail hrows (exp_cohort_entry_tail p ops input row u ts s hnot hrow entry) hm

theorem exp_scalar_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (entry : ExpCohortEntry p ops input row ts s) : ∀ a ∈ (expScalarFold ops input row ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact entry.good
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu]))
      (exp_cohort_entry_tail p ops input row t ts s hnot (hb t (by simp)) entry)

theorem exp_lane_step_native (ops : Ops α) (input : Nat → Nat → α)
    (row t u : Nat) (s : State α) (hb : t/1024=row) (hi : MaxNativeIndices u s) :
    MaxNativeIndices u (expLaneStep ops input row t s) := by
  have he : row*1024+t%1024=t := by omega
  by_cases h : u=t
  · subst u
    simpa only [expLaneStep,he] using exp_prefix_native ops input row (t%1024) s (by simpa only [he] using hi)
  · exact exp_prefix_native_other ops input row (t%1024) u s (by simpa only [he] using h) hi

theorem exp_scalar_fold_native (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (u : Nat) (hb : ∀ t ∈ ts, t/1024=row)
    (hi : MaxNativeIndices u s) : MaxNativeIndices u (expScalarFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact hi
  | cons t ts ih =>
    exact ih _ (by intro t ht; exact hb t (by simp [ht]))
      (exp_lane_step_native ops input row t u s (hb t (by simp)) hi)

theorem exp_scalar_fold_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) : (expScalarFold ops input row ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    exact (ih (expLaneStep ops input row t s)).trans (exp_prefix_epochs ops input row (t%1024) s)

#print axioms exp_lane_step_native
#print axioms exp_scalar_fold_native
#print axioms exp_scalar_fold_epochs
#print axioms exp_lane_entry_of_cohort
#print axioms exp_lane_step_run
#print axioms exp_lane_step_other
#print axioms exp_cohort_entry_tail
#print axioms exp_scalar_fold_run
#print axioms exp_scalar_fold_other
#print axioms exp_scalar_fold_member_pc
#print axioms exp_scalar_fold_member_sum
#print axioms exp_scalar_fold_good
end LarkNativeSoftmax
