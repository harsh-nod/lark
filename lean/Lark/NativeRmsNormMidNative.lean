import Lark.NativeRmsNormMidFold

/-! Bind the scale-entry fold to native physical waves and their first logical
cohort. Inactive physical lanes remain at the actual second block barrier.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def midNative (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  midEntryFold row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row warp 64) s

theorem mid_native_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (hw : warp < 16) (ready : MidReady p ops input row s) :
    (cohortThreads row warp 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s =
      some (midNative ops input row warp s) := by
  have hi : ∀ lane, lane < 64 → NativeIndices (cohortBase row warp + lane) s := by
    intro lane hl
    simpa only [cohortBase, Nat.add_assoc] using ready.indices (warp * 64 + lane) (by omega)
  have hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 39 := by
    intro lane hl
    simpa only [cohortBase, Nat.add_assoc] using ready.pc (warp * 64 + lane) (by omega)
  apply mid_fold_run p ops row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row warp 64) s (cohort_nodup row warp 64)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro t ht ha
    have hm := Nat.mod_le (t % 1024) 64
    omega
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (hi lane hl).2.1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (hi lane hl).2.2.1
  · intro t ht ha
    have hm := Nat.mod_le (t % 1024) 64
    exact ready.partials (t % 1024 % 64) (by omega)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact hp lane hl

theorem mid_native_preserves (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) :
    (midNative ops input row warp s).memory = s.memory ∧
    (midNative ops input row warp s).indices = s.indices ∧
    (midNative ops input row warp s).epochs = s.epochs :=
  mid_fold_preserves row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row warp 64) s

theorem mid_native_pc (ops : Ops α) (input : Nat → Nat → α) (row warp lane : Nat) (s : State α)
    (hw : warp < 16) (hl : lane < 64) :
    (midNative ops input row warp s).pc (cohortBase row warp + lane) =
      if warp * 64 + lane < 16 then 41 else 55 := by
  have h := mid_fold_pc row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row warp 64) s (cohort_nodup row warp 64)
    (cohortBase row warp + lane) ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)
  simpa only [(cohort_arithmetic row warp lane hw hl).2.1] using h

theorem mid_native_acc (ops : Ops α) (input : Nat → Nat → α) (row lane : Nat) (s : State α) (hl : lane < 16) :
    (midNative ops input row 0 s).regs (cohortBase row 0 + lane) 0 = some (warpSum ops input row lane) := by
  have hc := cohort_arithmetic row 0 lane (by decide) (by omega)
  have ha : (cohortBase row 0 + lane) % 1024 < 16 := by
    rewrite [hc.2.1]
    simpa only [Nat.zero_mul, Nat.zero_add] using hl
  have h := mid_fold_acc row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row 0 64) s (cohort_nodup row 0 64)
    (cohortBase row 0 + lane) ((cohort_mem row 0 64 _).mpr ⟨lane, by omega, rfl⟩) ha
  simpa only [hc.2.2.1] using h

theorem mid_native_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    StageReady p row 0 16 41 16 (.const 16) (warpSum ops input row) (midNative ops input row 0 s) := by
  have hi := (mid_native_preserves ops input row 0 s).2.1
  constructor
  · intro lane hl
    simpa only [Nat.zero_mul, Nat.zero_add, hl, ↓reduceIte] using mid_native_pc ops input row 0 lane s (by decide) (by omega)
  · intro lane hl
    have h : NativeIndices (cohortBase row 0 + lane) s := by
      simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using ready.indices lane (by omega)
    have hc := (cohort_arithmetic row 0 lane (by decide) (by omega)).2.2.1
    exact (congrFun (congrFun hi (cohortBase row 0 + lane)) 2).trans (by simpa only [hc] using h.2.2.1)
  · intro lane hl
    exact LarkReduction.int32_cast 16 (by decide)
  · intro lane hl
    exact mid_native_acc ops input row lane s hl

theorem mid_native_inactive (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) (s : State α)
    (ht : 16 ≤ tid) (hb : tid < 64) : (midNative ops input row 0 s).pc (cohortBase row 0 + tid) = 55 := by
  have h := mid_native_pc ops input row 0 tid s (by decide) hb
  simpa only [Nat.zero_mul, Nat.zero_add, show ¬ tid < 16 by omega, ↓reduceIte] using h

theorem mid_native_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (s : State α) (hw : warp < 16) (ready : MidReady p ops input row s) :
    ∀ access ∈ (midNative ops input row warp s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  apply mid_fold_good p row (fun t => t % 1024) (fun t => t % 1024 % 64)
    (fun t => warpSum ops input row (t % 1024 % 64)) (cohortThreads row warp 64) s
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    simpa only [cohortBase, Nat.add_assoc] using ready.epoch (warp * 64 + lane) (by omega)
  · exact ready.good

#print axioms mid_native_run
#print axioms mid_native_ready
#print axioms mid_native_inactive
#print axioms mid_native_good
end LarkNativeRmsNorm
