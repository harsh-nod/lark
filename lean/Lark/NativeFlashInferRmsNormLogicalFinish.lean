import Lark.NativeFlashInferRmsNormTopFold

/-! Fifth logical32 snapshot/add and the unique tid-zero total store. The
actual physical64 fold also visits all parked lanes before block convergence.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def logicalLast (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) : State α :=
  topFold ops (waveLeft p values) (waveRight p values) (cohortThreads row 0 32)
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s)

theorem logical_last_fold (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (ready : MixedReady row 42 values s) (hi : ∀ t ∈ cohortThreads row 0 32, NativeIndices t s) :
    (cohortThreads row 0 32).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u)
      (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) = some (logicalLast p ops row values s) := by
  apply top_fold_run p ops (waveLeft p values) (waveRight p values) _ _ (cohort_nodup row 0 32)
  · intro t ht; exact hi t ht
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact (xor_shuffled_fields p row 0 32 1 lane values s (by decide) (by decide) hl).1.trans
      (congrArg (· + 1) (ready.active.pc lane hl))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    change _ = some (values (LarkPartitionCollective.nativeLane (geometry p) (cohortBase row 0 + lane)))
    rewrite [(cohort_coords p row 0 lane (by decide) (by omega)).2]
    exact (xor_shuffled_fields p row 0 32 1 lane values s (by decide) (by decide) hl).2.1.trans (ready.active.accumulator lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    change _ = some (values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) (cohortBase row 0 + lane)) 1))
    rewrite [(cohort_coords p row 0 lane (by decide) (by omega)).2]
    exact (xor_shuffled_fields p row 0 32 1 lane values s (by decide) (by decide) hl).2.2

theorem logical_last_other (p : Shape) (ops : Ops α) (row t : Nat) (values : Nat → α)
    (s : State α) (ht : t ∉ cohortThreads row 0 32) :
    (logicalLast p ops row values s).pc t = s.pc t ∧ (logicalLast p ops row values s).regs t = s.regs t := by
  have h := top_fold_other ops (waveLeft p values) (waveRight p values) (cohortThreads row 0 32) t
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) ht
  have hs := xor_shuffled_other p row 0 32 1 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem logical_last_run (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (ready : MixedReady row 42 values s) (hi : ∀ t ∈ cohortThreads row 0 32, NativeIndices t s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 32) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (logicalLast p ops row values s) := by
  apply shuffle_physical_fold p ops row s _
  · rewrite [cohort_xor_shuffle p row 0 32 1 42 s values (by decide) (Or.inl rfl) (by decide)
      ready.active.pc ready.active.accumulator (by decide)]
    exact logical_last_fold p ops row values s ready hi
  · intro tid hl hu
    exact (logical_last_other p ops row (cohortBase row 0 + tid) values s (upper_not_active row tid hl)).1.trans
      (ready.inactive tid hl hu)

theorem logical_last_pc (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (inactive : ∀ tid, 32 ≤ tid → tid < 64 → s.pc (cohortBase row 0 + tid) = 46)
    (lane : Nat) (hl : lane < 64) : (logicalLast p ops row values s).pc (cohortBase row 0 + lane) = 46 := by
  by_cases ha : lane < 32
  · exact (top_fold_member ops (waveLeft p values) (waveRight p values) _ _ (cohort_nodup row 0 32) _
      ((cohort_mem row 0 32 _).mpr ⟨lane, ha, rfl⟩)).1
  · exact (logical_last_other p ops row (cohortBase row 0 + lane) values s (upper_not_active row lane (by omega))).1.trans
      (inactive lane (by omega) hl)

theorem logical_last_total (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) :
    (logicalLast p ops row values s).memory (partialSlot row 0) = some (ops.add (values 0) (values (xorPeer32 0 1))) := by
  have coords := cohort_arithmetic row 0 0 (by decide) (by decide)
  have h := top_fold_value ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) (cohort_nodup row 0 32)
    (cohortBase row 0 + 0) ((cohort_mem row 0 32 _).mpr ⟨0, by decide, rfl⟩)
    (by simp only [coords.2.1, Nat.zero_mul, Nat.zero_add])
  simpa only [waveLeft, waveRight, (cohort_coords p row 0 0 (by decide) (by decide)).2,
    topCell, partialCell, coords.1, partialSlot] using h

theorem logical_last_preserves (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) :
    (logicalLast p ops row values s).indices = s.indices ∧ (logicalLast p ops row values s).epochs = s.epochs :=
  top_fold_preserves ops (waveLeft p values) (waveRight p values) (cohortThreads row 0 32)
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s)

theorem logical_last_memory_frame (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (l : Location) (hl : l ≠ partialSlot row 0) : (logicalLast p ops row values s).memory l = s.memory l := by
  apply top_fold_memory_other ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) l
  intro t ht hw
  obtain ⟨lane, hla, rfl⟩ := (cohort_mem row 0 32 t).mp ht
  have hr := (cohort_arithmetic row 0 lane (by decide) (by omega)).1
  exact hl (hw.2.trans (by simp only [topCell, partialCell, hr, partialSlot]))

theorem logical_last_good (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (he : ∀ t ∈ cohortThreads row 0 32, (s.epochs t).block = 1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (logicalLast p ops row values s).trace, Good a :=
  top_fold_good ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) he good

theorem cohort_second_barrier (row warp active : Nat) (s : State α) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = 46) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp active) s = none ∧
    LarkCollective.converged program (cohortThreads row warp active) s = some .block := by
  have hp0 : s.pc (cohortBase row warp) = 46 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp active).filter (LarkPartitionCollective.isShuffle program s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [LarkPartitionCollective.isShuffle, hp lane hl, second_barrier]
  have ha : (cohortThreads row warp active).all (fun t => s.pc t == s.pc (cohortBase row warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [hp lane hl, hp0]
  constructor
  · simp [LarkPartitionCollective.nextCohort, hf]
  · unfold LarkCollective.converged
    rewrite [cohort_head row warp active hpos]
    simp only [bind, pure, Option.bind, ha, ↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0, second_barrier]
    rfl

theorem warp_at_second_barrier (p : Shape) (ops : Ops α) (row warp active extra : Nat)
    (s next : State α) (hpos : 0 < active)
    (hfold : (cohortThreads row warp active).foldlM
      (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) s = some next)
    (hp : ∀ lane, lane < active → next.pc (cohortBase row warp + lane) = 46) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (cohortThreads row warp active) (extra + 1) s = some next := by
  obtain ⟨hc, hconverged⟩ := cohort_second_barrier row warp active next hpos hp
  rewrite [LarkPartitionCollective.runWarp, hfold]
  simp only [bind, pure, Option.some_bind, hc, hconverged, reduceCtorEq, ↓reduceIte]

theorem logical_last_warp (p : Shape) (ops : Ops α) (row extra : Nat) (values : Nat → α)
    (s : State α) (ready : MixedReady row 42 values s) (hi : ∀ t ∈ cohortThreads row 0 32, NativeIndices t s) :
    continueCohort p ops (cohortThreads row 0 64) (extra + 1) s = some (logicalLast p ops row values s) := by
  have hc := mixed_next row 42 values s ready .xor 1 0 (.const 1) (by decide)
  have hshuffle := cohort_xor_shuffle p row 0 32 1 42 s values (by decide) (Or.inl rfl) (by decide)
    ready.active.pc ready.active.accumulator (by decide)
  have hfold := logical_last_run p ops row values s ready hi
  rewrite [hshuffle] at hfold
  rewrite [continue_shuffle p ops _ _ (extra + 1) s hc, hshuffle]
  change LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
    (cohortThreads row 0 64) (extra + 1) (shuffleUpdates 1 (xorSnapshot p row 0 32 1 values) s) = _
  exact warp_at_second_barrier p ops row 0 64 extra _ _ (by decide) hfold
    (logical_last_pc p ops row values s ready.inactive)

#print axioms logical_last_fold
#print axioms logical_last_other
#print axioms logical_last_run
#print axioms logical_last_total
#print axioms logical_last_preserves
#print axioms logical_last_memory_frame
#print axioms logical_last_good
#print axioms cohort_second_barrier
#print axioms logical_last_warp
end LarkNativeFlashInferRmsNorm
