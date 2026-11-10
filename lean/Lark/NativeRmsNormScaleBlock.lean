import Lark.NativeRmsNormSkipFold

/-! The actual middle block phase: the scale wave followed by fifteen inactive
physical waves, in the scheduler's original order and native geometry.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scaleBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  skipWaves row (List.range' 1 15) (scaleWave p ops input row s)

theorem scale_block_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleBlock p ops input row s).indices = s.indices ∧
    (scaleBlock p ops input row s).epochs = s.epochs := by
  have h := skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)
  have h1 := scale_wave_preserves p ops input row s
  exact ⟨h.2.1.trans h1.1, h.2.2.2.1.trans h1.2⟩

theorem scale_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleBlock p ops input row s).memory (scaleSlot row) = some (scale ops input row) :=
  (congrFun (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).1 _).trans
    (scale_wave_value p ops input row s)

theorem scale_block_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l ≠ scaleSlot row) :
    (scaleBlock p ops input row s).memory l = s.memory l :=
  (congrFun (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).1 l).trans
    (scale_wave_memory_other p ops input row s l hl)

theorem scale_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) : Reads p input (scaleBlock p ops input row s) := by
  constructor
  · intro i hi
    exact (scale_block_memory_other p ops input row s (globalCell 1 i) (by simp [globalCell, scaleSlot])).trans (reads.1 i hi)
  · intro i hi
    exact (scale_block_memory_other p ops input row s (globalCell 2 i) (by simp [globalCell, scaleSlot])).trans (reads.2 i hi)

theorem scale_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α)
    (ready : MidReady p ops input row s) :
    ∀ access ∈ (scaleBlock p ops input row s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  have ht := (skip_waves_preserves row (List.range' 1 15) (scaleWave p ops input row s)).2.2.2.2
  intro access ha
  exact scale_wave_good p ops input row s ready access (ht ▸ ha)

theorem scale_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) (ready : MidReady p ops input row s) :
    (scaleBlock p ops input row s).pc (row * 1024 + tid) = 55 := by
  have hw : tid / 64 < 16 := by omega
  have hl : tid % 64 < 64 := Nat.mod_lt _ (by decide)
  have he : cohortBase row (tid / 64) + tid % 64 = row * 1024 + tid := by
    unfold cohortBase
    have hd := Nat.div_add_mod tid 64
    omega
  by_cases hz : tid / 64 = 0
  · have ht64 : tid < 64 := by omega
    have hf := skip_waves_other row (List.range' 1 15) (scaleWave p ops input row s)
      (cohortBase row 0 + tid) (by
        intro w hm
        have hm := List.mem_range'.mp hm
        exact cohort_disjoint row 0 w tid ht64 (by omega))
    have hp := hf.trans (scale_wave_pc p ops input row s ready tid ht64)
    simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using hp
  · have hm : tid / 64 ∈ List.range' 1 15 := List.mem_range'.mpr ⟨tid / 64 - 1, by omega, by omega⟩
    have hp := skip_waves_pc row (List.range' 1 15) (scaleWave p ops input row s)
      (by decide) (tid / 64) (tid % 64) hm hl
    simpa only [he] using hp

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
  · intro w hw lane hl
    have h := List.mem_range'.mp hw
    have hi := (scale_wave_preserves p ops input row s).1
    have hn : NativeIndices (cohortBase row w + lane) s := by
      simpa only [cohortBase, Nat.add_assoc] using ready.indices (w * 64 + lane) (by omega)
    have hc := (cohort_arithmetic row w lane (by omega) hl).2.1
    exact (congrFun (congrFun hi (cohortBase row w + lane)) 1).trans (by simpa only [hc] using hn.2.1)
  · intro w hw lane hl
    have h := List.mem_range'.mp hw
    have hf := (scale_wave_other p ops input row (cohortBase row w + lane) s
      (cohort_disjoint row w 0 lane hl (by omega))).1
    exact hf.trans (by simpa only [cohortBase, Nat.add_assoc] using ready.pc (w * 64 + lane) (by omega))

#print axioms scale_block_fold_run
#print axioms scale_block_cut
#print axioms scale_block_value
#print axioms scale_block_good
end LarkNativeRmsNorm
