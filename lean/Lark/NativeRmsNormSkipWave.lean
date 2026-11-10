import Lark.NativeRmsNormScaleWave

/-! The other fifteen physical waves take the source's inactive branch. They
execute PC 39 and park at PC 55 without adding a memory access or changing data.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def skipLanes (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => advance s t 55) s

theorem skip_lanes_preserves (ts : List Nat) (s : State α) :
    (skipLanes ts s).memory = s.memory ∧ (skipLanes ts s).indices = s.indices ∧
    (skipLanes ts s).regs = s.regs ∧ (skipLanes ts s).epochs = s.epochs ∧
    (skipLanes ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons t ts ih => exact ih (advance s t 55)

theorem skip_lanes_other (ts : List Nat) (s : State α) (t : Nat) (ht : t ∉ ts) :
    (skipLanes ts s).pc t = s.pc t := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      have he : t ≠ u := by intro he; subst t; simp at ht
      exact (ih (advance s u 55) hn).trans (by simp [advance, he])

theorem skip_lanes_pc (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (skipLanes ts s).pc t = 55 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (skip_lanes_other ts (advance s u 55) u hnot).trans (by simp [advance])
      · exact ih (advance s u 55) hnodup hm

theorem skip_lanes_run (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (ht : ∀ t ∈ ts, 16 ≤ t % 1024)
    (hi : ∀ t ∈ ts, s.indices t 1 = some (t % 1024 : Nat))
    (hp : ∀ t ∈ ts, s.pc t = 39) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (skipLanes ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rewrite [List.foldlM_cons, mid_enter_inactive p ops t (t % 1024) s
        (by have h := ht t (by simp); omega) (hi t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (advance s t 55) hnodup
      · intro u hu; exact ht u (by simp [hu])
      · intro u hu; exact hi u (by simp [hu])
      · intro u hu
        have he : u ≠ t := by intro he; subst u; exact hnot hu
        exact (show (advance s t 55).pc u = s.pc u by simp [advance, he]).trans (hp u (by simp [hu]))

def skipWave (row warp : Nat) (s : State α) : State α := skipLanes (cohortThreads row warp 64) s

theorem skip_wave_run (p : Shape) (ops : Ops α) (row warp : Nat) (s : State α)
    (hw : 0 < warp) (hb : warp < 16)
    (hi : ∀ lane, lane < 64 → s.indices (cohortBase row warp + lane) 1 = some (warp * 64 + lane : Nat))
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 39) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp s = some (skipWave row warp s) := by
  rewrite [cohort_native_threads p row warp hb, show fuel.warp = 7 + 1 by decide]
  apply warp_at_second_barrier p ops row warp 64 7 s (skipWave row warp s) (by decide)
  · apply skip_lanes_run p ops _ s (cohort_nodup row warp 64)
    · intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
      rewrite [(cohort_arithmetic row warp lane hb hl).2.1]
      omega
    · intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
      simpa only [(cohort_arithmetic row warp lane hb hl).2.1] using hi lane hl
    · intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
      exact hp lane hl
  · intro lane hl
    exact skip_lanes_pc _ s (cohort_nodup row warp 64) _ ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)

#print axioms skip_lanes_run
#print axioms skip_wave_run
end LarkNativeRmsNorm
