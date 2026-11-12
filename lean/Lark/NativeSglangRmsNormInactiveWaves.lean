import Lark.NativeSglangRmsNormWaveSecond

/-! The remaining physical waves skip the second reduction without reading
shared memory. This remains valid after wave0 has overwritten the partials
with inverse values. No premise about the overwritten partials is required.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot

def skipFold (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => advance s t 76) s

theorem skip_fold_cons (t : Nat) (ts : List Nat) (s : State α) :
    skipFold (t::ts) s=skipFold ts (advance s t 76) := rfl

theorem skip_fold_preserves (ts : List Nat) (s : State α) :
    (skipFold ts s).memory=s.memory ∧ (skipFold ts s).indices=s.indices ∧
    (skipFold ts s).regs=s.regs ∧ (skipFold ts s).epochs=s.epochs ∧ (skipFold ts s).trace=s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons t ts ih => exact ih (advance s t 76)

theorem skip_fold_other (ts : List Nat) (t : Nat) (s : State α) (ht : t∉ts) :
    (skipFold ts s).pc t=s.pc t := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
      have hn : t∉ts := by intro hm; exact ht (by simp [hm])
      have hne : t≠u := by intro he; subst t; simp at ht
      exact (ih (advance s u 76) hn).trans (by simp [advance,hne])

theorem skip_fold_member (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t∈ts) :
    (skipFold ts s).pc t=76 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (skip_fold_other ts u (advance s u 76) hnot).trans (by simp [advance])
      · exact ih (advance s u 76) hnodup hm

theorem skip_fold_run (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (inactive : ∀ t∈ts,t%1024/32≠0)
    (hi : ∀ t∈ts,NativeIndices t s) (hp : ∀ t∈ts,s.pc t=57) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (skipFold ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have lane : LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=
          some (advance s t 76) := second_inactive_lane p ops t (t%1024/32) 510 s (inactive t (by simp))
            (hi t (by simp)).2.2.2 (hp t (by simp))
      rw [List.foldlM_cons,lane]
      apply ih (advance s t 76) hnodup
      · intro u hu; exact inactive u (by simp [hu])
      · intro u hu; exact hi u (by simp [hu])
      · intro u hu
        have hne : u≠t := by intro he; subst u; exact hnot hu
        simpa only [advance,if_neg hne] using hp u (by simp [hu])

theorem native_inactive_wave (p : Shape) (ops : Ops α) (row w n : Nat) (s : State α)
    (hw : w<16) (hpos : 0<w) (hi : ∀ t∈cohortThreads row w 64,NativeIndices t s)
    (hp : ∀ t∈cohortThreads row w 64,s.pc t=57) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row w) (n+1) s=some (skipFold (cohortThreads row w 64) s) := by
  have inactive : ∀ t∈cohortThreads row w 64,t%1024/32≠0 := by
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
    rw [(cohort_arithmetic row w lane hw hl).2.1]
    omega
  rw [cohort_native_threads p row w hw,run_warp_continue,
    skip_fold_run p ops _ s (cohort_nodup row w 64) inactive hi hp]
  simp only [Option.some_bind]
  have hpc := fun t ht => skip_fold_member (cohortThreads row w 64) s (cohort_nodup row w 64) t ht
  have hn : cohortThreads row w 64≠[] := by
    intro he
    have hh := cohort_head row w 64 (by decide)
    rw [he] at hh
    cases hh
  unfold continueCohort
  rw [second_barrier_next_none _ _ hpc,second_barrier_converged _ _ hn hpc]
  rfl

def inactiveWaves (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => skipFold (cohortThreads row w 64) s) s

theorem inactive_waves_cons (row w : Nat) (ws : List Nat) (s : State α) :
    inactiveWaves row (w::ws) s=inactiveWaves row ws (skipFold (cohortThreads row w 64) s) := rfl

theorem inactive_waves_preserves (row : Nat) (ws : List Nat) (s : State α) :
    (inactiveWaves row ws s).memory=s.memory ∧ (inactiveWaves row ws s).indices=s.indices ∧
    (inactiveWaves row ws s).regs=s.regs ∧ (inactiveWaves row ws s).epochs=s.epochs ∧
    (inactiveWaves row ws s).trace=s.trace := by
  induction ws generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons w ws ih =>
      have h := ih (skipFold (cohortThreads row w 64) s)
      have hs := skip_fold_preserves (cohortThreads row w 64) s
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.1.trans hs.2.2.1,
        h.2.2.2.1.trans hs.2.2.2.1,h.2.2.2.2.trans hs.2.2.2.2⟩

theorem inactive_waves_other (row : Nat) (ws : List Nat) (t : Nat) (s : State α)
    (outside : ∀ w∈ws,t∉cohortThreads row w 64) :
    (inactiveWaves row ws s).pc t=s.pc t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (skipFold (cohortThreads row w 64) s) (fun v hv => outside v (by simp [hv]))).trans
        (skip_fold_other (cohortThreads row w 64) t s (outside w (by simp)))

theorem inactive_waves_member_pc (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup)
    (w lane : Nat) (hw : w∈ws) (hl : lane<64) :
    (inactiveWaves row ws s).pc (cohortBase row w+lane)=76 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons v ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hw with he | hm
      · subst w
        have outside : ∀ u∈ws,cohortBase row v+lane∉cohortThreads row u 64 := by
          intro u hu
          apply distinct_cohorts row v u _ _ ((cohort_mem row v 64 _).mpr ⟨lane,hl,rfl⟩)
          intro he; subst u; exact hnot hu
        exact (inactive_waves_other row ws _ (skipFold (cohortThreads row v 64) s) outside).trans
          (skip_fold_member _ s (cohort_nodup row v 64) _ ((cohort_mem row v 64 _).mpr ⟨lane,hl,rfl⟩))
      · exact ih (skipFold (cohortThreads row v 64) s) hnodup hm

theorem inactive_waves_run (p : Shape) (ops : Ops α) (row : Nat) (ws : List Nat) (s : State α)
    (hn : ws.Nodup) (bounds : ∀ w∈ws,0<w ∧ w<16)
    (hi : ∀ w∈ws,∀ t∈cohortThreads row w 64,NativeIndices t s)
    (hp : ∀ w∈ws,∀ t∈cohortThreads row w 64,s.pc t=57) :
    ws.foldlM (fun u w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) row w) fuel.warp u) s=some (inactiveWaves row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have lane : LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
          (warpThreads (geometry p) row w) fuel.warp s=some (skipFold (cohortThreads row w 64) s) :=
        native_inactive_wave p ops row w 7 s (bounds w (by simp)).2 (bounds w (by simp)).1
          (hi w (by simp)) (hp w (by simp))
      rw [List.foldlM_cons,lane]
      apply ih (skipFold (cohortThreads row w 64) s) hnodup
      · intro v hv; exact bounds v (by simp [hv])
      · intro v hv t ht
        simpa only [NativeIndices,(skip_fold_preserves (cohortThreads row w 64) s).2.1] using hi v (by simp [hv]) t ht
      · intro v hv t ht
        have hne : v≠w := by intro he; subst v; exact hnot hv
        exact (skip_fold_other _ _ s (distinct_cohorts row v w t hne ht)).trans (hp v (by simp [hv]) t ht)

#print axioms skip_fold_cons
#print axioms skip_fold_preserves
#print axioms skip_fold_other
#print axioms skip_fold_member
#print axioms skip_fold_run
#print axioms native_inactive_wave
#print axioms inactive_waves_cons
#print axioms inactive_waves_preserves
#print axioms inactive_waves_other
#print axioms inactive_waves_member_pc
#print axioms inactive_waves_run
end LarkNativeSglangRmsNorm
