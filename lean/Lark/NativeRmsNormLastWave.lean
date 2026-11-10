import Lark.NativeRmsNormLastFold

/-! Execute the final native-wave shuffle and guarded lane fold to the first
block barrier, including its exact shared partial and access classification.
This is the wave tail; full six-stage and block composition remain separate.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def lastWave (p : Shape) (ops : Ops α) (row warp valid : Nat) (values : Nat → α) (s : State α) : State α :=
  let lanes := LarkPartitionCollective.nativeLane (geometry p)
  firstLastFold ops warp valid lanes (fun t => values (lanes t))
    (fun t => values (downPeer 64 32 (lanes t))) (cohortThreads row warp 64)
    (shuffleUpdates 1 (cohortSnapshot p row warp 64 32 values) s)

theorem last_wave_run (p : Shape) (ops : Ops α) (row warp valid : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16)
    (ready : StageReady p row warp 64 33 valid (.ivar 4) values s)
    (hi3 : ∀ lane, lane < 64 → s.indices (cohortBase row warp + lane) 3 = some (warp : Int)) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) s).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (lastWave p ops row warp valid values s) := by
  rewrite [cohort_down_shuffle p row warp 64 32 33 s values hw (by decide) (by decide) (by decide)
    (by decide) ready.pc ready.acc (first_shuffle 5 (by decide))]
  simp only [Option.some_bind]
  apply first_last_fold_run p ops warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64) _ (cohort_nodup row warp 64) hw
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact ready.lane lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact hi3 lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact ready.valid lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact (cohort_shuffled_fields p row warp 64 32 lane values s hw (by decide) hl).2.1.trans (ready.acc lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact (cohort_shuffled_fields p row warp 64 32 lane values s hw (by decide) hl).2.2
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rewrite [(cohort_shuffled_fields p row warp 64 32 lane values s hw (by decide) hl).1, ready.pc lane hl]
    rfl

theorem last_wave_preserves (p : Shape) (ops : Ops α) (row warp valid : Nat)
    (values : Nat → α) (s : State α) :
    (lastWave p ops row warp valid values s).indices = s.indices ∧
    (lastWave p ops row warp valid values s).epochs = s.epochs :=
  first_last_fold_preserves ops warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64) _

theorem last_wave_fields (p : Shape) (ops : Ops α) (row warp valid lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hl : lane < 64)
    (ha : s.regs (cohortBase row warp + lane) 0 = some (values lane)) :
    (lastWave p ops row warp valid values s).pc (cohortBase row warp + lane) = 38 ∧
    (lastWave p ops row warp valid values s).regs (cohortBase row warp + lane) 0 =
      some (if lane + 32 < valid then ops.add (values lane) (values (downPeer 64 32 lane)) else values lane) := by
  have hc := (cohort_coords p row warp lane hw hl).2
  have hacc : (shuffleUpdates 1 (cohortSnapshot p row warp 64 32 values) s).regs
      (cohortBase row warp + lane) 0 = some (values (LarkPartitionCollective.nativeLane (geometry p)
        (cohortBase row warp + lane))) := by
    rewrite [hc]
    exact (cohort_shuffled_fields p row warp 64 32 lane values s hw (by decide) hl).2.1.trans ha
  have h := first_last_fold_member ops warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64) _ (cohort_nodup row warp 64) (cohortBase row warp + lane)
    ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩) hacc
  simpa only [hc] using h

theorem last_wave_partial (p : Shape) (ops : Ops α) (row warp valid : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) :
    (lastWave p ops row warp valid values s).memory (partialCell (cohortBase row warp) warp) =
      some (if 32 < valid then ops.add (values 0) (values 32) else values 0) := by
  have hc : LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp) = 0 := by
    simpa only [Nat.add_zero] using (cohort_coords p row warp 0 hw (by decide)).2
  have h := last_cohort_partial p ops row warp valid
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (shuffleUpdates 1 (cohortSnapshot p row warp 64 32 values) s) hw
  simpa only [hc, downPeer, Nat.zero_add, show 32 < 64 by decide, ↓reduceIte] using h

theorem last_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp valid : Nat)
    (values : Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (lastWave p ops row warp valid values s) :=
  first_last_fold_reads p ops input warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64) _ reads

theorem last_wave_good (p : Shape) (ops : Ops α) (row warp valid : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16)
    (he : ∀ lane, lane < 64 → (s.epochs (cohortBase row warp + lane)).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (lastWave p ops row warp valid values s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  apply first_last_fold_good p ops warp valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 64 32 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp 64)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    rfl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (cohort_arithmetic row warp lane hw hl).2.2.2.symm
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact he lane hl
  · exact good

/-- A cohort whose actual PCs all name the first block barrier has no shuffle
cohort and converges to the real block cut. -/
theorem cohort_first_barrier (row warp width : Nat) (s : State α) (hpos : 0 < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = 38) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp width) s = none ∧
    LarkCollective.converged program (cohortThreads row warp width) s = some .block := by
  have hp0 : s.pc (cohortBase row warp) = 38 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp width).filter (LarkPartitionCollective.isShuffle program s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [LarkPartitionCollective.isShuffle, hp lane hl, first_barrier]
  have ha : (cohortThreads row warp width).all (fun t => s.pc t == s.pc (cohortBase row warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [hp lane hl, hp0]
  constructor
  · simp [LarkPartitionCollective.nextCohort, hf]
  · unfold LarkCollective.converged
    rewrite [cohort_head row warp width hpos]
    simp only [bind, pure, Option.bind, ha, ↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0, first_barrier]
    rfl

theorem warp_at_first_barrier (p : Shape) (ops : Ops α) (row warp width extra : Nat)
    (s next : State α) (hpos : 0 < width)
    (hfold : (cohortThreads row warp width).foldlM
      (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) s = some next)
    (hp : ∀ lane, lane < width → next.pc (cohortBase row warp + lane) = 38) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (cohortThreads row warp width) (extra + 1) s = some next := by
  rcases cohort_first_barrier row warp width next hpos hp with ⟨hcohort, hconverged⟩
  rewrite [LarkPartitionCollective.runWarp, hfold]
  simp only [bind, pure, Option.some_bind, hcohort, hconverged, reduceCtorEq, ↓reduceIte]

/-- The actual scheduler completes the sixth snapshot shuffle and all source
lane tails at the block barrier; no shuffle is treated as a memory fence. -/
theorem last_wave_warp (p : Shape) (ops : Ops α) (row warp valid extra : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16)
    (ready : StageReady p row warp 64 33 valid (.ivar 4) values s)
    (hi3 : ∀ lane, lane < 64 → s.indices (cohortBase row warp + lane) 3 = some (warp : Int)) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) s).bind
      fun shuffled => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (cohortThreads row warp 64) (extra + 1) shuffled) =
      some (lastWave p ops row warp valid values s) := by
  have hs := cohort_down_shuffle p row warp 64 32 33 s values hw (by decide) (by decide) (by decide)
    (by decide) ready.pc ready.acc (first_shuffle 5 (by decide))
  have hf := last_wave_run p ops row warp valid values s hw ready hi3
  rewrite [hs, Option.some_bind] at hf
  rewrite [hs, Option.some_bind]
  exact warp_at_first_barrier p ops row warp 64 extra _ (lastWave p ops row warp valid values s)
    (by decide) hf (fun lane hl => (last_wave_fields p ops row warp valid lane values s hw hl (ready.acc lane hl)).1)

#print axioms last_wave_run
#print axioms last_wave_partial
#print axioms last_wave_good
#print axioms cohort_first_barrier
#print axioms last_wave_warp
end LarkNativeRmsNorm
