import Lark.NativeRmsNormPartial

/-! Sequential execution of the final wave stage through its shared partial store.
The six-stage wave and whole-block composition are separate obligations.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstLastFold (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => firstLastAfter ops t (lane t) warp valid (a t) (b t) s) s

theorem first_last_fold_preserves (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α) :
    (firstLastFold ops warp valid lane a b ts s).indices = s.indices ∧
    (firstLastFold ops warp valid lane a b ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (firstLastAfter ops t (lane t) warp valid (a t) (b t) s)
      have h1 := first_last_fields ops t (lane t) warp valid (a t) (b t) s
      exact ⟨h.1.trans h1.2.1, h.2.trans h1.2.2⟩

theorem first_last_fold_other (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (firstLastFold ops warp valid lane a b ts s).pc t = s.pc t ∧
    (firstLastFold ops warp valid lane a b ts s).regs t = s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have h := ih (firstLastAfter ops u (lane u) warp valid (a u) (b u) s) hn
      have h1 := first_last_other ops u t (lane u) warp valid (a u) (b u) s hne
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem first_last_fold_member (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat)
    (ht : t ∈ ts) (ha : s.regs t 0 = some (a t)) :
    (firstLastFold ops warp valid lane a b ts s).pc t = 38 ∧
    (firstLastFold ops warp valid lane a b ts s).regs t 0 =
      some (if lane t + 32 < valid then ops.add (a t) (b t) else a t) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := first_last_fold_other ops warp valid lane a b ts u
          (firstLastAfter ops u (lane u) warp valid (a u) (b u) s) hnot
        exact ⟨h.1.trans (first_last_fields ops u (lane u) warp valid (a u) (b u) s).1,
          (congrFun h.2 0).trans (first_last_acc ops u (lane u) warp valid (a u) (b u) s ha)⟩
      · have hne : t ≠ u := by intro he; subst t; exact hnot hm
        have hr := first_last_other ops u t (lane u) warp valid (a u) (b u) s hne
        exact ih (firstLastAfter ops u (lane u) warp valid (a u) (b u) s) hnodup hm
          ((congrFun hr.2 0).trans ha)

theorem first_last_fold_run (p : Shape) (ops : Ops α) (warp valid : Nat)
    (lane : Nat → Nat) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (hw : warp < 16) (hl : ∀ t ∈ ts, lane t < 64)
    (hi2 : ∀ t ∈ ts, s.indices t 2 = some (lane t : Int))
    (hi3 : ∀ t ∈ ts, s.indices t 3 = some (warp : Int))
    (hv : ∀ t ∈ ts, s.indices t 4 = some (valid : Int))
    (ha : ∀ t ∈ ts, s.regs t 0 = some (a t)) (hb : ∀ t ∈ ts, s.regs t 1 = some (b t))
    (hp : ∀ t ∈ ts, s.pc t = 34) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (firstLastFold ops warp valid lane a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      let next := firstLastAfter ops t (lane t) warp valid (a t) (b t) s
      have hpres := first_last_fields ops t (lane t) warp valid (a t) (b t) s
      have hother : ∀ u ∈ ts, next.pc u = s.pc u ∧ next.regs u = s.regs u := by
        intro u hu
        exact first_last_other ops t u (lane t) warp valid (a t) (b t) s
          (by intro he; subst u; exact hnot hu)
      rewrite [List.foldlM_cons, first_last_lane p ops t (lane t) warp valid (a t) (b t) s
        (hl t (by simp)) hw (hi2 t (by simp)) (hi3 t (by simp)) (hv t (by simp))
        (ha t (by simp)) (hb t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih next hnodup
      · intro u hu; exact hl u (by simp [hu])
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 2).trans (hi2 u (by simp [hu]))
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 3).trans (hi3 u (by simp [hu]))
      · intro u hu; exact (congrFun (congrFun hpres.2.1 u) 4).trans (hv u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 0).trans (ha u (by simp [hu]))
      · intro u hu; exact (congrFun (hother u hu).2 1).trans (hb u (by simp [hu]))
      · intro u hu; exact (hother u hu).1.trans (hp u (by simp [hu]))

theorem first_last_fold_memory_nonzero (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α) (hz : ∀ t ∈ ts, lane t ≠ 0) :
    (firstLastFold ops warp valid lane a b ts s).memory = s.memory := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (firstLastAfter ops t (lane t) warp valid (a t) (b t) s)
        (by intro u hu; exact hz u (by simp [hu]))).trans
        (first_last_memory_nonzero ops t (lane t) warp valid (a t) (b t) s (hz t (by simp)))

theorem first_last_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (warp valid : Nat) (lane : Nat → Nat) (a b : Nat → α) (ts : List Nat) (s : State α)
    (reads : Reads p input s) : Reads p input (firstLastFold ops warp valid lane a b ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih _ (first_last_reads p ops input t (lane t) warp valid (a t) (b t) s reads)

theorem first_last_fold_good (p : Shape) (ops : Ops α) (warp valid : Nat) (lane : Nat → Nat)
    (a b : Nat → α) (ts : List Nat) (s : State α)
    (hl : ∀ t ∈ ts, lane t = (t % 1024) % 64)
    (hw : ∀ t ∈ ts, warp = (t % 1024) / 64)
    (he : ∀ t ∈ ts, (s.epochs t).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (firstLastFold ops warp valid lane a b ts s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      have hp := (first_last_fields ops t (lane t) warp valid (a t) (b t) s).2.2
      apply ih (firstLastAfter ops t (lane t) warp valid (a t) (b t) s)
      · intro u hu; exact hl u (by simp [hu])
      · intro u hu; exact hw u (by simp [hu])
      · intro u hu
        exact (congrArg (fun epochs => (epochs u).block) hp).trans (he u (by simp [hu]))
      · exact first_last_good p ops t (lane t) warp valid (a t) (b t) s
          (hl t (by simp)) (hw t (by simp)) (he t (by simp)) good

theorem cohort_cons : cohortThreads row warp 64 = cohortBase row warp ::
    (List.range 63).map (fun lane => cohortBase row warp + (lane + 1)) := by
  have hr : List.range 64 = 0 :: (List.range 63).map (fun lane => lane + 1) := by decide
  simp only [cohortThreads, hr, List.map_cons, List.map_map, Nat.add_zero]
  rfl

/-- Lane zero writes the partial; every subsequent cohort lane leaves memory unchanged. -/
theorem last_cohort_partial (p : Shape) (ops : Ops α) (row warp valid : Nat) (a b : Nat → α)
    (s : State α) (hw : warp < 16) :
    (firstLastFold ops warp valid (LarkPartitionCollective.nativeLane (geometry p)) a b
      (cohortThreads row warp 64) s).memory (partialCell (cohortBase row warp) warp) =
      some (if 32 < valid then ops.add (a (cohortBase row warp)) (b (cohortBase row warp))
        else a (cohortBase row warp)) := by
  let tail := (List.range 63).map (fun lane => cohortBase row warp + (lane + 1))
  have hnonzero : ∀ t ∈ tail, LarkPartitionCollective.nativeLane (geometry p) t ≠ 0 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := List.mem_map.mp ht
    have hl := List.mem_range.mp hl
    rewrite [(cohort_coords p row warp (lane + 1) hw (by omega)).2]
    omega
  have hc : LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp) = 0 := by
    simpa only [Nat.add_zero] using (cohort_coords p row warp 0 hw (by decide)).2
  have hm := first_last_fold_memory_nonzero ops warp valid
    (LarkPartitionCollective.nativeLane (geometry p)) a b tail
    (firstLastAfter ops (cohortBase row warp) 0 warp valid
      (a (cohortBase row warp)) (b (cohortBase row warp)) s) hnonzero
  unfold firstLastFold
  rewrite [cohort_cons, List.foldl_cons, hc]
  exact (congrFun hm _).trans (first_last_value ops (cohortBase row warp) warp valid _ _ s)

#print axioms first_last_fold_run
#print axioms first_last_fold_member
#print axioms first_last_fold_reads
#print axioms first_last_fold_good
#print axioms last_cohort_partial
end LarkNativeRmsNorm
