import Lark.NativeFusedRmsNormSkip

/-! Sequential visits to all inactive physical waves after wave zero finishes.
They preserve the final total and all values/trace/epochs already established.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def skipWaves (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => skipWave row w s) s

theorem skip_waves_preserves (row : Nat) (ws : List Nat) (s : State α) :
    (skipWaves row ws s).memory = s.memory ∧ (skipWaves row ws s).indices = s.indices ∧
    (skipWaves row ws s).regs = s.regs ∧ (skipWaves row ws s).epochs = s.epochs ∧ (skipWaves row ws s).trace = s.trace := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons w ws ih =>
      have h := ih (skipWave row w s)
      have h1 := skip_fold_preserves (cohortThreads row w 64) s
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.1.trans h1.2.2.1,
        h.2.2.2.1.trans h1.2.2.2.1, h.2.2.2.2.trans h1.2.2.2.2⟩

theorem skip_waves_other (row : Nat) (ws : List Nat) (s : State α) (t : Nat)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) : (skipWaves row ws s).pc t = s.pc t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (skipWave row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
        (skip_fold_other (cohortThreads row w 64) t s (ht w (by simp)))

theorem skip_waves_pc (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup)
    (warp lane : Nat) (hw : warp ∈ ws) (hl : lane < 64) :
    (skipWaves row ws s).pc (cohortBase row warp + lane) = 50 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        exact (skip_waves_other row ws (skipWave row w s) _ (by
          intro u hu; exact cohort_disjoint row w u lane hl (by intro he; subst u; exact hnot hu))).trans
          (skip_fold_member _ s (cohort_nodup row w 64) _ ((cohort_mem row w 64 _).mpr ⟨lane, hl, rfl⟩))
      · exact ih (skipWave row w s) hnodup hm

theorem skip_waves_run (p : Shape) (ops : Ops α) (row : Nat) (ws : List Nat) (s : State α)
    (hn : ws.Nodup) (hb : ∀ w ∈ ws, 0 < w ∧ w < 16)
    (hp : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, s.pc t = 36)
    (hi : ∀ w ∈ ws, ∀ t ∈ cohortThreads row w 64, NativeIndices t s) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (skipWaves row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rewrite [List.foldlM_cons, skip_wave_run p ops row w s (hb w (by simp)).1 (hb w (by simp)).2
        (hp w (by simp)) (hi w (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (skipWave row w s) hnodup (by intro u hu; exact hb u (by simp [hu]))
      · intro u hu t ht
        have hne : u ≠ w := by intro he; subst u; exact hnot hu
        exact (skip_fold_other (cohortThreads row w 64) t s (cohorts_disjoint row u w t hne ht)).trans
          (hp u (by simp [hu]) t ht)
      · intro u hu t ht
        simpa only [NativeIndices, (skip_fold_preserves (cohortThreads row w 64) s).2.1] using hi u (by simp [hu]) t ht

#print axioms skip_waves_preserves
#print axioms skip_waves_other
#print axioms skip_waves_pc
#print axioms skip_waves_run
end LarkNativeFusedRmsNorm
