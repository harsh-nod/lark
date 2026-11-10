import Lark.NativeRmsNormSkipWave

/-! Source-ordered composition of the inactive physical waves. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def skipWaves (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s warp => skipWave row warp s) s

theorem skip_waves_preserves (row : Nat) (ws : List Nat) (s : State α) :
    (skipWaves row ws s).memory = s.memory ∧ (skipWaves row ws s).indices = s.indices ∧
    (skipWaves row ws s).regs = s.regs ∧ (skipWaves row ws s).epochs = s.epochs ∧
    (skipWaves row ws s).trace = s.trace := by
  induction ws generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons w ws ih =>
      have h := ih (skipWave row w s)
      have h1 := skip_lanes_preserves (cohortThreads row w 64) s
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.1.trans h1.2.2.1,
        h.2.2.2.1.trans h1.2.2.2.1, h.2.2.2.2.trans h1.2.2.2.2⟩

theorem skip_waves_other (row : Nat) (ws : List Nat) (s : State α) (t : Nat)
    (ht : ∀ w ∈ ws, t ∉ cohortThreads row w 64) : (skipWaves row ws s).pc t = s.pc t := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (skipWave row w s) (by intro u hu; exact ht u (by simp [hu]))).trans
        (skip_lanes_other _ s t (ht w (by simp)))

theorem skip_waves_pc (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup)
    (warp lane : Nat) (hw : warp ∈ ws) (hl : lane < 64) :
    (skipWaves row ws s).pc (cohortBase row warp + lane) = 55 := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hw with he | hm
      · subst warp
        have ht : ∀ u ∈ ws, cohortBase row w + lane ∉ cohortThreads row u 64 := by
          intro u hu
          exact cohort_disjoint row w u lane hl (by intro he; subst u; exact hnot hu)
        exact (skip_waves_other row ws (skipWave row w s) _ ht).trans
          (skip_lanes_pc _ s (cohort_nodup row w 64) _ ((cohort_mem row w 64 _).mpr ⟨lane, hl, rfl⟩))
      · exact ih (skipWave row w s) hnodup hm

theorem skip_waves_run (p : Shape) (ops : Ops α) (row : Nat) (ws : List Nat) (s : State α)
    (hn : ws.Nodup) (hb : ∀ w ∈ ws, 0 < w ∧ w < 16)
    (hi : ∀ w ∈ ws, ∀ lane, lane < 64 →
      s.indices (cohortBase row w + lane) 1 = some (w * 64 + lane : Nat))
    (hp : ∀ w ∈ ws, ∀ lane, lane < 64 → s.pc (cohortBase row w + lane) = 39) :
    ws.foldlM (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row w) fuel.warp s) s = some (skipWaves row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hpres := skip_lanes_preserves (cohortThreads row w 64) s
      rewrite [List.foldlM_cons, skip_wave_run p ops row w s (hb w (by simp)).1 (hb w (by simp)).2
        (hi w (by simp)) (hp w (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (skipWave row w s) hnodup (by intro u hu; exact hb u (by simp [hu]))
      · intro u hu lane hl
        exact (congrFun (congrFun hpres.2.1 (cohortBase row u + lane)) 1).trans (hi u (by simp [hu]) lane hl)
      · intro u hu lane hl
        have ht := cohort_disjoint row u w lane hl (by intro he; subst u; exact hnot hu)
        exact (skip_lanes_other _ s _ ht).trans (hp u (by simp [hu]) lane hl)

#print axioms skip_waves_run
#print axioms skip_waves_pc
#print axioms skip_waves_preserves
end LarkNativeRmsNorm
