import Lark.NativeFlashInferRmsNormMidFold

/-! Bind the entry fold to the native physical cohorts. Only the lower32 of
wave zero load partials; upper32 and all fifteen other waves park at PC46.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def midNative (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  midEntryFold row (blockPartial ops input row) (cohortThreads row warp 64) s

theorem mid_native_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (hw : warp < 16) (ready : MidReady p ops input row s) :
    (cohortThreads row warp 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s =
      some (midNative ops input row warp s) := by
  apply mid_fold_run p ops row (blockPartial ops input row) _ s (cohort_nodup row warp 64)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    have hi := ready.indices (warp * 64 + lane) (by omega)
    simpa only [cohortBase, Nat.add_assoc, (cohort_arithmetic row warp lane hw hl).2.1] using hi.2.1
  · intro t ht ha; exact ready.partials (t % 1024) ha
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    simpa only [cohortBase, Nat.add_assoc] using ready.pc (warp * 64 + lane) (by omega)

theorem mid_native_preserves (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (midNative ops input row warp s).memory = s.memory ∧
    (midNative ops input row warp s).indices = s.indices ∧ (midNative ops input row warp s).epochs = s.epochs :=
  mid_fold_preserves row (blockPartial ops input row) (cohortThreads row warp 64) s

theorem mid_native_pc (ops : Ops α) (input : Nat → Nat → α) (row warp lane : Nat) (s : State α)
    (hw : warp < 16) (hl : lane < 64) :
    (midNative ops input row warp s).pc (cohortBase row warp + lane) =
      if warp * 64 + lane < 32 then 34 else 46 := by
  have h := mid_fold_pc row (blockPartial ops input row) (cohortThreads row warp 64) s
    (cohort_nodup row warp 64) _ ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)
  simpa only [(cohort_arithmetic row warp lane hw hl).2.1] using h

theorem mid_native_acc (ops : Ops α) (input : Nat → Nat → α) (row lane : Nat) (s : State α) (hl : lane < 32) :
    (midNative ops input row 0 s).regs (cohortBase row 0 + lane) 0 = some (blockPartial ops input row lane) := by
  have hc := cohort_arithmetic row 0 lane (by decide) (by omega)
  have ha : (cohortBase row 0 + lane) % 1024 < 32 := by simpa only [hc.2.1, Nat.zero_mul, Nat.zero_add] using hl
  simpa only [hc.2.1, Nat.zero_mul, Nat.zero_add] using
    mid_fold_acc row (blockPartial ops input row) (cohortThreads row 0 64) s (cohort_nodup row 0 64) _
      ((cohort_mem row 0 64 _).mpr ⟨lane, by omega, rfl⟩) ha

theorem mid_native_inactive (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α)
    (ht : 32 ≤ tid) (hb : tid < 64) : (midNative ops input row 0 s).pc (cohortBase row 0 + tid) = 46 := by
  simpa only [Nat.zero_mul, Nat.zero_add, show ¬ tid < 32 by omega, ↓reduceIte] using
    mid_native_pc ops input row 0 tid s (by decide) hb

theorem mid_native_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (hw : warp < 16) (ready : MidReady p ops input row s) :
    ∀ a ∈ (midNative ops input row warp s).trace, Good a := by
  apply mid_fold_good row (blockPartial ops input row) (cohortThreads row warp 64) s
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    simpa only [cohortBase, Nat.add_assoc] using ready.epoch (warp * 64 + lane) (by omega)
  · exact ready.good

#print axioms mid_native_run
#print axioms mid_native_preserves
#print axioms mid_native_pc
#print axioms mid_native_acc
#print axioms mid_native_inactive
#print axioms mid_native_good
end LarkNativeFlashInferRmsNorm
