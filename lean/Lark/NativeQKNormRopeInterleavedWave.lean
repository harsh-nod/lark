import Lark.NativeQKNormRopeInterleavedFold
import Lark.NativeQKNormRopeHalt
import Lark.NativeQKNormRopeFrames

/-! Complete actual interleaved physical-wave execution from native entry to
halt, with every owned output, actual trace classification and race freedom. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedWaveState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : State α :=
  interleavedFold ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s)

theorem native_interleaved_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4) (hr : Reads p input s) :
    (cohortThreads block warp 64).foldlM
      (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program false) t fuel.lane s)
      (fifthSnapshot p ops input block warp s) = some (interleavedWaveState p ops input block warp s) := by
  apply interleaved_fold_run p ops input _ _ _ _ (cohort_nodup block warp 64)
    (cohort_bound p block warp 64 hb hw (by decide))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact (fifth_snapshot_fields p ops input block warp lane s hw hl).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    simpa only [reductionA, Nat.add_sub_cancel_left] using (fifth_snapshot_fields p ops input block warp lane s hw hl).2.1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    simpa only [reductionB, Nat.add_sub_cancel_left] using (fifth_snapshot_fields p ops input block warp lane s hw hl).2.2
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact fifth_snapshot_values p ops input block warp lane s hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact fifth_snapshot_indices p ops input block warp lane s hl
  · simpa only [Reads, (fifth_snapshot_preserves p ops input block warp s).1] using hr

theorem interleaved_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) : (interleavedWaveState p ops input block warp s).pc (cohortBase block warp + lane) = 87 :=
  interleaved_fold_pc ops input _ _ _ _ (cohort_nodup block warp 64) _ ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)

theorem native_interleaved_wave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program false)
      (warpThreads (geometry p) block warp) fuel.warp s = some (interleavedWaveState p ops input block warp s) := by
  rw [native_fifth_snapshot p false ops input block warp s hb hw hp hr,
    show (11 : Nat) = 10 + 1 by decide, run_warp_continue, native_interleaved_fold p ops input block warp s hb hw hr]
  change continueCohort p false ops (cohortThreads block warp 64) 10 (interleavedWaveState p ops input block warp s) = _
  exact continue_at_final_halt p false ops block warp 64 10 _ (by decide)
    (fun lane hl => interleaved_wave_pc p ops input block warp lane s hl)

theorem interleaved_wave_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat)
    (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (interleavedWaveState p ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (interleavedOutput ops input
        (fun r => normalizedValue ops input t (weightBuffer t) (normalScale ops (waveValues ops input block warp 5 lane)) r) t e)) := by
  have result := interleaved_fold_value ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s) (cohort_nodup block warp 64)
    (cohortBase block warp + lane) e ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩) he
  have total : waveValues ops input block warp 5 lane = ops.add (waveValues ops input block warp 4 lane)
      (waveValues ops input block warp 4 (xorPeer32 lane 1)) := rfl
  simpa only [interleavedResult, interleavedNormals, reductionA, reductionB, Nat.add_sub_cancel_left, total] using result

theorem interleaved_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (interleavedWaveState p ops input block warp s) := by
  apply interleaved_fold_reads
  simpa only [Reads, (fifth_snapshot_preserves p ops input block warp s).1] using hr

theorem interleaved_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : (interleavedWaveState p ops input block warp s).epochs = s.epochs :=
  (interleaved_fold_epochs ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s)).trans
    (fifth_snapshot_preserves p ops input block warp s).2.1

theorem interleaved_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (loc : Location) (hn : ∀ t ∈ cohortThreads block warp 64, loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (interleavedWaveState p ops input block warp s).memory loc = s.memory loc :=
  (interleaved_fold_memory_frame ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s) loc hn).trans
    (congrFun (fifth_snapshot_preserves p ops input block warp s).1 loc)

theorem interleaved_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp t : Nat)
    (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (interleavedWaveState p ops input block warp s).pc t = s.pc t ∧
    (interleavedWaveState p ops input block warp s).indices t = s.indices t ∧
    (interleavedWaveState p ops input block warp s).regs t = s.regs t := by
  have sf := fifth_snapshot_other p ops input block warp t s ht
  have tf := interleaved_fold_other ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) t (fifthSnapshot p ops input block warp s) ht
  exact ⟨tf.1.trans sf.1, tf.2.1.trans sf.2.1, tf.2.2.trans sf.2.2⟩

theorem interleaved_wave_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : (interleavedWaveState p ops input block warp s).trace.length = s.trace.length + 1024 := by
  change (interleavedFold ops input _ _ _ _).trace.length = _
  rw [interleaved_fold_trace_length, (fifth_snapshot_preserves p ops input block warp s).2.2, prepare_fold_trace_length]
  have len : (cohortThreads block warp 64).length = 64 := by simp [cohortThreads]
  rw [len]

theorem interleaved_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedWaveState p ops input block warp s).trace, Good access := by
  apply interleaved_fold_good
  have preparedGood := prepare_fold_good ops input (cohortThreads block warp 64) s good
  simpa only [(fifth_snapshot_preserves p ops input block warp s).2.2] using preparedGood

theorem interleaved_wave_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry p) (interleavedWaveState p ops input block warp (initial (layout p) input outside)).trace = true :=
  race_free p _ (interleaved_wave_good p ops input block warp _ (by intro access ha; cases ha))

#print axioms native_interleaved_fold
#print axioms interleaved_wave_pc
#print axioms native_interleaved_wave
#print axioms interleaved_wave_value
#print axioms interleaved_wave_reads
#print axioms interleaved_wave_epochs
#print axioms interleaved_wave_memory_frame
#print axioms interleaved_wave_other
#print axioms interleaved_wave_trace_length
#print axioms interleaved_wave_good
#print axioms interleaved_wave_initial_race_free
end LarkNativeQKNormRope
