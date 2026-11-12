import Lark.NativeSglangRmsNormReductionSnapshots

/-! Successful initialized native-wave execution through the fifth XOR
snapshot, with four additions complete. The last addition and shared store
remain explicit at PC53. No algebraic or prior-trace safety premise is used.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot

def waveBaseValues (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : Nat → α :=
  fun lane => threadSum ops input row (warp*64+lane)

def waveLastSnapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : State α :=
  reductionSnapshot p ops row warp (waveBaseValues ops input row warp) (wavePrepared ops input row warp s) 4

theorem wave_snapshot_zero (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    reductionSnapshot p ops row warp (waveBaseValues ops input row warp) (wavePrepared ops input row warp s) 0 =
      firstSnapshot p ops input row warp s := by
  simp only [reductionSnapshot,firstSnapshot,waveBaseValues]
  rfl

theorem wave_prepared_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads p input s) :
    (wavePrepared ops input row warp s).regs (cohortBase row warp+lane) 0 =
      some (waveBaseValues ops input row warp lane) := by
  have h := (wave_prepared_ready p ops input row warp lane s reads hl).accumulator
  have coords := cohort_arithmetic row warp lane hw hl
  simpa only [coords.1,coords.2.1,waveBaseValues] using h

theorem wave_last_snapshot_success (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row warp : Nat) (s : State α)
    (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads p input s) :
    (((warpThreads (geometry p) row warp).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s).bind
      (LarkPartitionCollective.runShuffle (geometry p) (program repaired) (cohortThreads row warp 64))).bind
      (runSnapshotPairs p repaired ops row warp 4) = some (waveLastSnapshot p ops input row warp s) := by
  rw [wave_entry_success p repaired ops input row warp s hr hw hp reads]
  simp only [Option.some_bind]
  rw [← wave_snapshot_zero p ops input row warp s]
  exact snapshot_pairs_success p repaired ops row warp 4 _ _ hw (by decide)
    (fun lane hl => (wave_prepared_ready p ops input row warp lane s reads hl).pc)
    (fun lane hl => wave_prepared_accumulator p ops input row warp lane s hw hl reads)

theorem wave_last_snapshot_native (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row warp : Nat) (s : State α)
    (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) fuel.warp s =
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) 3 (waveLastSnapshot p ops input row warp s) := by
  change LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
    (warpThreads (geometry p) row warp) 8 s = _
  rw [wave_first_snapshot_step p repaired ops input row warp 7 s hr hw hp reads]
  rw [← wave_snapshot_zero p ops input row warp s]
  change LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
    (cohortThreads row warp 64) (3+4)
    (reductionSnapshot p ops row warp (waveBaseValues ops input row warp) (wavePrepared ops input row warp s) 0) = _
  exact native_reduction_four p repaired ops row warp 3 _ _ hw
    (fun lane hl => (wave_prepared_ready p ops input row warp lane s reads hl).pc)
    (fun lane hl => wave_prepared_accumulator p ops input row warp lane s hw hl reads)

theorem wave_last_snapshot_fields (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads p input s) :
    (waveLastSnapshot p ops input row warp s).pc (cohortBase row warp+lane) = 53 ∧
    (waveLastSnapshot p ops input row warp s).regs (cohortBase row warp+lane) 0 =
      some (reductionValues ops (waveBaseValues ops input row warp) 4 lane) ∧
    (waveLastSnapshot p ops input row warp s).regs (cohortBase row warp+lane) 1 =
      some (reductionValues ops (waveBaseValues ops input row warp) 4 (xorPeer32 lane 1)) :=
  reduction_snapshot_fields p ops row warp 4 lane _ _ hw hl
    (fun lane hl => (wave_prepared_ready p ops input row warp lane s reads hl).pc)
    (fun lane hl => wave_prepared_accumulator p ops input row warp lane s hw hl reads)

theorem wave_last_snapshot_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (waveLastSnapshot p ops input row warp s).memory = (wavePrepared ops input row warp s).memory ∧
    (waveLastSnapshot p ops input row warp s).indices = (wavePrepared ops input row warp s).indices ∧
    (waveLastSnapshot p ops input row warp s).epochs = s.epochs ∧
    (waveLastSnapshot p ops input row warp s).trace = (wavePrepared ops input row warp s).trace := by
  have h := reduction_snapshot_preserves p ops row warp 4 (waveBaseValues ops input row warp) (wavePrepared ops input row warp s)
  exact ⟨h.1,h.2.1,h.2.2.1.trans (prefix_fold_epochs ops input _ s),h.2.2.2⟩

theorem wave_last_snapshot_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hl : lane < 64) (reads : Reads p input s) :
    NativeIndices (cohortBase row warp+lane) (waveLastSnapshot p ops input row warp s) := by
  unfold NativeIndices
  rw [(wave_last_snapshot_preserves p ops input row warp s).2.1]
  exact (wave_prepared_ready p ops input row warp lane s reads hl).indices

theorem wave_last_snapshot_caches (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads p input s) :
    let t := cohortBase row warp+lane
    InputPrefix input row (warp*64+lane) 16 t (waveLastSnapshot p ops input row warp s) ∧
    WeightPrefix input (warp*64+lane) 16 t (waveLastSnapshot p ops input row warp s) := by
  have ready := wave_prepared_ready p ops input row warp lane s reads hl
  have coords := cohort_arithmetic row warp lane hw hl
  have h := And.intro ready.inputs ready.weights
  unfold InputPrefix WeightPrefix
  rw [(wave_last_snapshot_preserves p ops input row warp s).1]
  simpa only [InputPrefix,WeightPrefix,coords.1,coords.2.1] using h

theorem wave_last_snapshot_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (waveLastSnapshot p ops input row warp s) := by
  unfold Reads
  rw [(wave_last_snapshot_preserves p ops input row warp s).1]
  exact prefix_fold_reads p ops input _ s reads

theorem wave_last_snapshot_trace_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    ∃ events, (waveLastSnapshot p ops input row warp s).trace = events ++ s.trace ∧
      events.length = 5120 ∧ (∀ a ∈ events, Good a) := by
  rw [(wave_last_snapshot_preserves p ops input row warp s).2.2.2]
  simpa only [cohortThreads,List.length_map,List.length_range] using
    prefix_fold_trace_tail p ops input (cohortThreads row warp 64) s reads

theorem initial_wave_last_snapshot_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    raceFree (geometry p) (waveLastSnapshot p ops input row warp (initial p input outside)).trace = true := by
  rw [(wave_last_snapshot_preserves p ops input row warp _).2.2.2]
  exact initial_prefix_fold_race_free p ops input outside _

#print axioms wave_prepared_accumulator
#print axioms wave_snapshot_zero
#print axioms wave_last_snapshot_success
#print axioms wave_last_snapshot_native
#print axioms wave_last_snapshot_fields
#print axioms wave_last_snapshot_preserves
#print axioms wave_last_snapshot_indices
#print axioms wave_last_snapshot_caches
#print axioms wave_last_snapshot_reads
#print axioms wave_last_snapshot_trace_tail
#print axioms initial_wave_last_snapshot_race_free
end LarkNativeSglangRmsNorm
