import Lark.NativeFlashInferRmsNormScaleWave

/-! Actual inactive-wave visits after the total store. These proofs require
only source PCs/native indices, so they do not assume that the overwritten
partial0 still holds its old first-phase value.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def skipFold (ts : List Nat) (s : State α) : State α := ts.foldl (fun s t => advance s t 46) s
def skipWave (row warp : Nat) (s : State α) : State α := skipFold (cohortThreads row warp 64) s

theorem skip_fold_preserves (ts : List Nat) (s : State α) :
    (skipFold ts s).memory = s.memory ∧ (skipFold ts s).indices = s.indices ∧
    (skipFold ts s).regs = s.regs ∧ (skipFold ts s).epochs = s.epochs ∧ (skipFold ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons t ts ih => exact ih (advance s t 46)

theorem skip_fold_other (ts : List Nat) (t : Nat) (s : State α) (ht : t ∉ ts) :
    (skipFold ts s).pc t = s.pc t := by
  induction ts generalizing s with
  | nil => rfl
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      exact (ih (advance s u 46) hn).trans (by simp [advance, hne])

theorem skip_fold_member (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (skipFold ts s).pc t = 46 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (skip_fold_other ts u (advance s u 46) hnot).trans (by simp [advance])
      · exact ih (advance s u 46) hnodup hm

theorem skip_fold_run (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hp : ∀ t ∈ ts, s.pc t = 32) (hi : ∀ t ∈ ts, s.indices t 1 = some ((t % 1024 : Nat) : Int))
    (ha : ∀ t ∈ ts, 32 ≤ t % 1024) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (skipFold ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rewrite [List.foldlM_cons, mid_enter_inactive p ops t (t % 1024) s
        (by have h := ha t (by simp); omega) (hi t (by simp)) (hp t (by simp))]
      simp only [bind, Option.some_bind]
      apply ih (advance s t 46) hnodup
      · intro u hu
        have hne : u ≠ t := by intro he; subst u; exact hnot hu
        simpa only [advance, if_neg hne] using hp u (by simp [hu])
      · intro u hu; exact hi u (by simp [hu])
      · intro u hu; exact ha u (by simp [hu])

theorem skip_wave_run (p : Shape) (ops : Ops α) (row warp : Nat) (s : State α)
    (hw0 : 0 < warp) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 32)
    (hi : ∀ t ∈ cohortThreads row warp 64, NativeIndices t s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp s = some (skipWave row warp s) := by
  rewrite [cohort_native_threads p row warp hw, show fuel.warp = 7 + 1 by decide]
  apply warp_at_second_barrier p ops row warp 64 7 s _ (by decide)
  · apply skip_fold_run p ops _ s (cohort_nodup row warp 64) hp
    · intro t ht; exact (hi t ht).2.1
    · intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
      rewrite [(cohort_arithmetic row warp lane hw hl).2.1]
      omega
  · intro lane hl
    exact skip_fold_member _ s (cohort_nodup row warp 64) _ ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)

#print axioms skip_fold_preserves
#print axioms skip_fold_other
#print axioms skip_fold_member
#print axioms skip_fold_run
#print axioms skip_wave_run
end LarkNativeFlashInferRmsNorm
