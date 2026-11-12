import Lark.NativeFlashInferRmsNormSkipWaves

/-! Complete middle block phase in the source scheduler: wave zero performs
the logical32 reduction; all fifteen remaining native waves skip to PC46.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def scaleBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  skipWaves row (List.range' 1 15) (scaleWave p ops input row s)

theorem scale_block_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleBlock p ops input row s).indices = s.indices ∧ (scaleBlock p ops input row s).epochs = s.epochs := by
  have h := skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)
  have h1 := scale_wave_preserves p ops input row s
  exact ⟨h.2.1.trans h1.1, h.2.2.2.1.trans h1.2⟩

theorem scale_block_total (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleBlock p ops input row s).memory (partialSlot row 0) = some (blockSum ops input row) :=
  (congrFun (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).1 _).trans
    (scale_wave_total p ops input row s)

theorem scale_block_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l ≠ partialSlot row 0) :
    (scaleBlock p ops input row s).memory l = s.memory l :=
  (congrFun (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).1 l).trans
    (scale_wave_memory_frame p ops input row s l hl)

theorem scale_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) : ∀ a ∈ (scaleBlock p ops input row s).trace, Good a := by
  have ht := (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).2.2.2.2
  intro a ha
  exact scale_wave_good p ops input row s ready a (ht ▸ ha)

theorem scale_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) (ready : MidReady p ops input row s) :
    (scaleBlock p ops input row s).pc (row * 1024 + tid) = 46 := by
  have hw : tid / 64 < 16 := by omega
  have hl : tid % 64 < 64 := Nat.mod_lt _ (by decide)
  have he : cohortBase row (tid / 64) + tid % 64 = row * 1024 + tid := by unfold cohortBase; omega
  by_cases hz : tid / 64 = 0
  · have ht64 : tid < 64 := by omega
    have hf := skip_waves_other row (List.range' 1 15) (scaleWave p ops input row s) (cohortBase row 0 + tid) (by
      intro w hm
      have hm := List.mem_range'.mp hm
      exact cohort_disjoint row 0 w tid ht64 (by omega))
    simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using hf.trans (scale_wave_pc p ops input row s ready tid ht64)
  · have hm : tid / 64 ∈ List.range' 1 15 := List.mem_range'.mpr ⟨tid / 64 - 1, by omega, by omega⟩
    simpa only [he] using skip_waves_pc row (List.range' 1 15) (scaleWave p ops input row s)
      (by decide) (tid / 64) (tid % 64) hm hl

theorem scale_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    LarkCollective.converged program (blockThreads (geometry p) row) (scaleBlock p ops input row s) = some .block := by
  have hthreads : blockThreads (geometry p) row = cohortThreads row 0 1024 := by
    simp [blockThreads, geometry, cohortThreads, cohortBase]
  rewrite [hthreads]
  apply (cohort_second_barrier row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using scale_block_pc p ops input row tid s ht ready

theorem scale_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : MidReady p ops input row s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) s = some (scaleBlock p ops input row s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 16 := by
    change (1024 + 64 - 1) / 64 = 16
    decide
  have hlist : List.range 16 = 0 :: List.range' 1 15 := by decide
  rewrite [hcount, hlist, List.foldlM_cons, scale_wave_run p ops input row s ready]
  simp only [bind, Option.some_bind]
  apply skip_waves_run p ops row (List.range' 1 15) (scaleWave p ops input row s) (by decide)
  · intro w hw
    have h := List.mem_range'.mp hw
    omega
  · intro w hw t ht
    have h := List.mem_range'.mp hw
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row w 64 t).mp ht
    exact (scale_wave_other p ops input row _ s (cohort_disjoint row w 0 lane hl (by omega))).1.trans
      (by simpa only [cohortBase, Nat.add_assoc] using ready.pc (w * 64 + lane) (by omega))
  · intro w hw t ht
    have h := List.mem_range'.mp hw
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row w 64 t).mp ht
    simpa only [NativeIndices, (scale_wave_preserves p ops input row s).1, cohortBase, Nat.add_assoc] using
      ready.indices (w * 64 + lane) (by omega)

#print axioms scale_block_preserves
#print axioms scale_block_total
#print axioms scale_block_memory_frame
#print axioms scale_block_good
#print axioms scale_block_pc
#print axioms scale_block_cut
#print axioms scale_block_fold_run
end LarkNativeFlashInferRmsNorm
