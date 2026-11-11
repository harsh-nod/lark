import Lark.NativeFusedRmsNormLastFold

/-! Actual fifth logical32 shuffle and the two distinct partial stores in a
physical wave64. All lanes stop at the source's first block barrier.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def waveLeft (p : Shape) (values : Nat → α) (t : Nat) : α :=
  values (LarkPartitionCollective.nativeLane (geometry p) t)
def waveRight (p : Shape) (values : Nat → α) (t : Nat) : α :=
  values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) 1)
def lastWave (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α) (s : State α) : State α :=
  lastFold ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64)
    (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s)

structure LastReady (row warp : Nat) (values : Nat → α) (s : State α) : Prop where
  pc : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 31
  accumulator : ∀ lane, lane < 64 → s.regs (cohortBase row warp + lane) 0 = some (values lane)
  indices : ∀ t ∈ cohortThreads row warp 64, NativeIndices t s

theorem last_shuffled_fold (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (ready : LastReady row warp values s) :
    (cohortThreads row warp 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u)
      (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) =
      some (lastWave p ops row warp values s) := by
  apply last_fold_run p ops (waveLeft p values) (waveRight p values) _ _ (cohort_nodup row warp 64)
  · intro t ht; exact ready.indices t ht
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact (xor_shuffled_fields p row warp 64 1 lane values s hw (by decide) hl).1.trans
      (congrArg (· + 1) (ready.pc lane hl))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    change _ = some (values (LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp + lane)))
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact (xor_shuffled_fields p row warp 64 1 lane values s hw (by decide) hl).2.1.trans (ready.accumulator lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    change _ = some (values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp + lane)) 1))
    rewrite [(cohort_coords p row warp lane hw hl).2]
    exact (xor_shuffled_fields p row warp 64 1 lane values s hw (by decide) hl).2.2

theorem last_wave_pc (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α) (s : State α)
    (lane : Nat) (hl : lane < 64) : (lastWave p ops row warp values s).pc (cohortBase row warp + lane) = 35 :=
  (last_fold_member ops (waveLeft p values) (waveRight p values) _ _ (cohort_nodup row warp 64) _
    ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)).1

theorem last_wave_partial (p : Shape) (ops : Ops α) (row warp half : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hh : half < 2) :
    (lastWave p ops row warp values s).memory ⟨.shared, row, 0, warp * 2 + half⟩ =
      some (ops.add (values (half * 32)) (values (xorPeer32 (half * 32) 1))) := by
  let t := cohortBase row warp + half * 32
  have ht : t ∈ cohortThreads row warp 64 := (cohort_mem row warp 64 t).mpr ⟨half * 32, by omega, rfl⟩
  have hz : t % 1024 % 32 = 0 := by dsimp [t, cohortBase]; omega
  have coords := cohort_arithmetic row warp (half * 32) hw (by omega)
  have hlogical : t % 1024 / 32 = warp * 2 + half := by dsimp only [t]; rewrite [coords.2.1]; omega
  have h := last_fold_value ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) (cohort_nodup row warp 64) t ht hz
  simpa only [waveLeft, waveRight, t, (cohort_coords p row warp (half * 32) hw (by omega)).2,
    partialCell, coords.1, hlogical] using h

theorem last_wave_preserves (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α) (s : State α) :
    (lastWave p ops row warp values s).indices = s.indices ∧ (lastWave p ops row warp values s).epochs = s.epochs :=
  last_fold_preserves ops (waveLeft p values) (waveRight p values) (cohortThreads row warp 64)
    (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s)

theorem last_wave_memory_frame (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α) (s : State α)
    (l : Location) (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (lastWave p ops row warp values s).memory l = s.memory l := by
  apply last_fold_memory_other ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) l
  intro t ht hw
  rcases hl with hspace | hbuffer
  · have h := congrArg Location.space hw.2
    simp [hspace, partialCell] at h
  · exact hbuffer (by simpa only [partialCell] using congrArg Location.buffer hw.2)

theorem last_wave_good (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α) (s : State α)
    (he : ∀ t ∈ cohortThreads row warp 64, (s.epochs t).block = 0) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (lastWave p ops row warp values s).trace, Good a :=
  last_fold_good ops (waveLeft p values) (waveRight p values) _
    (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) he good

theorem cohort_first_barrier (row warp active : Nat) (s : State α) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = 35) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp active) s = none ∧
    LarkCollective.converged program (cohortThreads row warp active) s = some .block := by
  have hp0 : s.pc (cohortBase row warp) = 35 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp active).filter (LarkPartitionCollective.isShuffle program s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [LarkPartitionCollective.isShuffle, hp lane hl, first_barrier]
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
    rewrite [hp0, first_barrier]
    rfl

theorem warp_at_first_barrier (p : Shape) (ops : Ops α) (row warp active extra : Nat)
    (s next : State α) (hpos : 0 < active)
    (hfold : (cohortThreads row warp active).foldlM
      (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) s = some next)
    (hp : ∀ lane, lane < active → next.pc (cohortBase row warp + lane) = 35) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (cohortThreads row warp active) (extra + 1) s = some next := by
  obtain ⟨hc, hconverged⟩ := cohort_first_barrier row warp active next hpos hp
  rewrite [LarkPartitionCollective.runWarp, hfold]
  simp only [bind, pure, Option.some_bind, hc, hconverged, reduceCtorEq, ↓reduceIte]

theorem last_wave_warp (p : Shape) (ops : Ops α) (row warp extra : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (ready : LastReady row warp values s) :
    continueCohort p ops (cohortThreads row warp 64) (extra + 1) s = some (lastWave p ops row warp values s) := by
  have hc : LarkPartitionCollective.nextCohort program (cohortThreads row warp 64) s = some (cohortThreads row warp 64) := by
    apply cohort_next row warp 64 31 s (by decide) ready.pc
    intro t ht
    simp only [LarkPartitionCollective.isShuffle, ht]
    rfl
  rewrite [continue_shuffle p ops _ _ (extra + 1) s hc,
    cohort_xor_shuffle p row warp 64 1 31 s values hw (Or.inr rfl) (by decide) ready.pc ready.accumulator (by decide)]
  change LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
    (cohortThreads row warp 64) (extra + 1) (shuffleUpdates 1 (xorSnapshot p row warp 64 1 values) s) = _
  exact warp_at_first_barrier p ops row warp 64 extra _ _ (by decide)
    (last_shuffled_fold p ops row warp values s hw ready) (last_wave_pc p ops row warp values s)

#print axioms last_shuffled_fold
#print axioms last_wave_pc
#print axioms last_wave_partial
#print axioms last_wave_preserves
#print axioms last_wave_memory_frame
#print axioms last_wave_good
#print axioms cohort_first_barrier
#print axioms last_wave_warp
end LarkNativeFusedRmsNorm
