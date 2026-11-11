import Lark.NativeSoftmaxNormFrame

/-! Actual sequential normalization lane fold. Pending entries retain their
owned exponential inputs, shared total, native indices, controls and epoch.
The original unused clamp reads require only output presence, not old values. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormCohortEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) : Prop :=
  ∀ t ∈ ts, NormLaneEntry p ops input row (t%1024) s

def normLaneStep (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row t : Nat) (s : State α) : State α :=
  normLaneState guarded ops input row (t%1024) s

theorem norm_lane_step_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (entry : NormCohortEntry p ops input row ts s)
    (t : Nat) (ht : t ∈ ts) (hb : t/1024=row) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s=
      some (normLaneStep guarded ops input row t s) := by
  have h := norm_lane_run p guarded ops input row (t%1024) s (entry t ht)
  simpa only [show row*1024+t%1024=t by omega] using h

theorem norm_lane_step_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row t u : Nat) (s : State α) (hb : t/1024=row) (hu : u ≠ t) :
    OtherThread t u s (normLaneStep guarded ops input row t s) :=
  norm_lane_other guarded ops input row (t%1024) u s (by simpa only [show row*1024+t%1024=t by omega] using hu)

theorem norm_cohort_entry_tail (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (ts : List Nat) (s : State α) (hn : t ∉ ts) (hb : ∀ u ∈ t::ts, u/1024=row)
    (entry : NormCohortEntry p ops input row (t::ts) s) :
    NormCohortEntry p ops input row ts (normLaneStep guarded ops input row t s) := by
  intro u hu
  have hne : u%1024 ≠ t%1024 := by
    intro he
    have ht := hb t (by simp)
    have huro := hb u (by simp [hu])
    have hue : u=t := by omega
    subst u
    exact hn hu
  exact norm_lane_entry_other p guarded ops input row (t%1024) (u%1024) s hne
    (entry t (by simp)) (entry u (by simp [hu]))

def normScalarFold (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => normLaneStep guarded ops input row t s) s

theorem norm_scalar_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (entry : NormCohortEntry p ops input row ts s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s=
      some (normScalarFold guarded ops input row ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    rewrite [List.foldlM_cons,norm_lane_step_run p guarded ops input row (t::ts) s entry t (by simp) (hb t (by simp))]
    simp only [bind,Option.some_bind]
    exact ih _ htail (by intro u hu; exact hb u (by simp [hu])) (norm_cohort_entry_tail p guarded ops input row t ts s hnot hb entry)

theorem norm_scalar_fold_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hu : u ∉ ts) (hb : ∀ t ∈ ts, t/1024=row) :
    OtherThread u u s (normScalarFold guarded ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have hne : u ≠ t := by intro he; subst u; simp at hu
    exact other_thread_trans u u _ _ _ (norm_lane_step_other guarded ops input row t u s (hb t (by simp)) hne)
      (ih _ (by intro h; exact hu (by simp [h])) (by intro v hv; exact hb v (by simp [hv])))

theorem norm_scalar_fold_member_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (t : Nat) (ht : t ∈ ts) : (normScalarFold guarded ops input row ts s).pc t=normPc guarded 115 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hbs : ∀ v ∈ ts, v/1024=row := by intro v hv; exact hb v (by simp [hv])
    rcases List.mem_cons.mp ht with he | hm
    · subst t
      exact (norm_scalar_fold_other guarded ops input row ts u (normLaneStep guarded ops input row u s) hnot hbs).1.trans
        (by simpa only [show row*1024+u%1024=u by have h := hb u (by simp); omega] using norm_lane_pc guarded ops input row (u%1024) s)
    · exact ih _ htail hbs hm

theorem norm_scalar_fold_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) : (normScalarFold guarded ops input row ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih _).trans (norm_lane_epochs guarded ops input row (t%1024) s)

theorem norm_scalar_fold_entry_other (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (entry : NormCohortEntry p ops input row ts s) (u : Nat) (hu : u ∉ ts) (hrow : u/1024=row)
    (next : NormLaneEntry p ops input row (u%1024) s) :
    NormLaneEntry p ops input row (u%1024) (normScalarFold guarded ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact next
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hne : u%1024 ≠ t%1024 := by
      intro he
      have ht := hb t (by simp)
      have hue : u=t := by omega
      subst u
      exact hu (by simp)
    have next' := norm_lane_entry_other p guarded ops input row (t%1024) (u%1024) s hne (entry t (by simp)) next
    exact ih _ htail (by intro v hv; exact hb v (by simp [hv]))
      (norm_cohort_entry_tail p guarded ops input row t ts s hnot hb entry)
      (by intro he; exact hu (by simp [he])) next'

theorem norm_scalar_fold_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (entry : NormCohortEntry p ops input row ts s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normScalarFold true ops input row ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    exact ih _ htail (by intro v hv; exact hb v (by simp [hv]))
      (norm_cohort_entry_tail p true ops input row t ts s hnot hb entry)
      (norm_lane_fixed_good ops input row (t%1024) s (Nat.mod_lt _ (by decide)) (entry t (by simp)).epoch good)

#print axioms norm_lane_step_run
#print axioms norm_lane_step_other
#print axioms norm_cohort_entry_tail
#print axioms norm_scalar_fold_run
#print axioms norm_scalar_fold_other
#print axioms norm_scalar_fold_member_pc
#print axioms norm_scalar_fold_epochs
#print axioms norm_scalar_fold_entry_other
#print axioms norm_scalar_fold_fixed_good
end LarkNativeSoftmax
