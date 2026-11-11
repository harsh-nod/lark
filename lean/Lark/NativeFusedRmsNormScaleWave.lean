import Lark.NativeFusedRmsNormLogicalFinish

/-! Complete actual mixed physical wave zero during the block reduction: all
32 partial loads, five logical32 snapshot reductions and the unique total store.
The inactive upper32 are visited and stop at the second block barrier.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def scaleWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  logicalLast p ops row (logicalValues ops input row 4)
    (logicalStages p ops input row 0 4 (midNative ops input row 0 s))

theorem scale_last_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    MixedReady row 46 (logicalValues ops input row 4)
      (logicalStages p ops input row 0 4 (midNative ops input row 0 s)) :=
  logical_stages_ready p ops input row 0 4 _ (mid_mixed_ready p ops input row s ready)

theorem scale_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row 0) fuel.warp s = some (scaleWave p ops input row s) := by
  have hp := (logical_stages_preserves p ops input row 0 4 (midNative ops input row 0 s)).2.1.trans
    (mid_native_preserves ops input row 0 s).2.1
  have hi : ∀ t ∈ cohortThreads row 0 32,
      NativeIndices t (logicalStages p ops input row 0 4 (midNative ops input row 0 s)) := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    simpa only [NativeIndices, hp, cohortBase, Nat.zero_mul, Nat.add_zero] using ready.indices lane (by omega)
  rewrite [cohort_native_threads p row 0 (by decide), show fuel.warp = 7 + 1 by decide,
    run_warp_continue, mid_native_run p ops input row 0 s (by decide) ready]
  change continueCohort p ops (cohortThreads row 0 64) (3 + 4) (midNative ops input row 0 s) = _
  rewrite [logical_stages_run p ops input row 0 4 3 _ (by decide) (mid_mixed_ready p ops input row s ready)]
  exact logical_last_warp p ops row 2 _ _ (scale_last_ready p ops input row s ready) hi

theorem scale_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) (lane : Nat) (hl : lane < 64) :
    (scaleWave p ops input row s).pc (cohortBase row 0 + lane) = 50 :=
  logical_last_pc p ops row _ _ (scale_last_ready p ops input row s ready).inactive lane hl

theorem scale_wave_total (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleWave p ops input row s).memory (partialSlot row 0) = some (blockSum ops input row) :=
  logical_last_total p ops row (logicalValues ops input row 4) _

theorem scale_wave_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleWave p ops input row s).indices = s.indices ∧ (scaleWave p ops input row s).epochs = s.epochs := by
  have last := logical_last_preserves p ops row (logicalValues ops input row 4)
    (logicalStages p ops input row 0 4 (midNative ops input row 0 s))
  have stages := logical_stages_preserves p ops input row 0 4 (midNative ops input row 0 s)
  have entry := mid_native_preserves ops input row 0 s
  exact ⟨last.1.trans (stages.2.1.trans entry.2.1), last.2.trans (stages.2.2.1.trans entry.2.2)⟩

theorem scale_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α)
    (l : Location) (hl : l ≠ partialSlot row 0) : (scaleWave p ops input row s).memory l = s.memory l :=
  (logical_last_memory_frame p ops row (logicalValues ops input row 4) _ l hl).trans
    ((congrFun (logical_stages_preserves p ops input row 0 4 (midNative ops input row 0 s)).1 l).trans
      (congrFun (mid_native_preserves ops input row 0 s).1 l))

theorem active_subset_native (row t : Nat) (ht : t ∈ cohortThreads row 0 32) : t ∈ cohortThreads row 0 64 := by
  rewrite [physical_split]
  exact List.mem_append.mpr (Or.inl ht)

theorem scale_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ cohortThreads row 0 64) :
    (scaleWave p ops input row s).pc t = s.pc t ∧ (scaleWave p ops input row s).regs t = s.regs t := by
  have hactive : t ∉ cohortThreads row 0 32 := by intro hm; exact ht (active_subset_native row t hm)
  have h0 := mid_fold_other row (blockPartial ops input row) (cohortThreads row 0 64) t s ht
  have h1 := logical_stages_other p ops input row 0 4 t (midNative ops input row 0 s) hactive
  have h2 := logical_last_other p ops row t (logicalValues ops input row 4)
    (logicalStages p ops input row 0 4 (midNative ops input row 0 s)) hactive
  exact ⟨h2.1.trans (h1.1.trans h0.1), h2.2.trans (h1.2.trans h0.2)⟩

theorem scale_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    ∀ a ∈ (scaleWave p ops input row s).trace, Good a := by
  have hp := mid_native_preserves ops input row 0 s
  have hs := logical_stages_preserves p ops input row 0 4 (midNative ops input row 0 s)
  apply logical_last_good p ops row _ _
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    have he := ready.epoch lane (by omega)
    have ep := congrArg (fun epochs => (epochs (cohortBase row 0 + lane)).block) (hs.2.2.1.trans hp.2.2)
    exact ep.trans (by simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using he)
  · simpa only [hs.2.2.2] using mid_native_good p ops input row 0 s (by decide) ready

#print axioms scale_wave_run
#print axioms scale_wave_pc
#print axioms scale_wave_total
#print axioms scale_wave_preserves
#print axioms scale_wave_memory_frame
#print axioms scale_wave_other
#print axioms scale_wave_good
end LarkNativeFusedRmsNorm
