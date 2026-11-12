import Lark.NativeQKNormRopeNormalFold

/-! Actual split-half wave execution through normalization, parked at PC59.
The rotary exchanges, cache loads and stores remain a separate suffix. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def reductionA (ops : Ops α) (input : Nat → Nat → α) (block warp t : Nat) : α :=
  waveValues ops input block warp 4 (t - cohortBase block warp)
def reductionB (ops : Ops α) (input : Nat → Nat → α) (block warp t : Nat) : α :=
  waveValues ops input block warp 4 (xorPeer32 (t - cohortBase block warp) 1)

def normalWaveState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : State α :=
  normalFold ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s)

theorem native_normal_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hw : warp < 4) (hr : Reads p input s) :
    (cohortThreads block warp 64).foldlM
      (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s)
      (fifthSnapshot p ops input block warp s) = some (normalWaveState p ops input block warp s) := by
  apply normal_fold_run p ops input _ _ _ _ (cohort_nodup block warp 64)
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

theorem native_normalization_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) block warp) fuel.warp s =
      continueCohort p true ops (cohortThreads block warp 64) 10 (normalWaveState p ops input block warp s) := by
  rw [native_fifth_snapshot p true ops input block warp s hb hw hp hr]
  rw [show (11 : Nat) = 10 + 1 by decide, run_warp_continue, native_normal_fold p ops input block warp s hw hr]
  rfl

theorem normal_wave_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    NormalReady ops input (cohortBase block warp + lane)
      (reductionA ops input block warp (cohortBase block warp + lane))
      (reductionB ops input block warp (cohortBase block warp + lane)) (normalWaveState p ops input block warp s) := by
  apply normal_fold_member ops input _ _ _ _ (cohort_nodup block warp 64)
    (cohortBase block warp + lane) ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)
  intro t ht
  obtain ⟨peer, hpeer, rfl⟩ := (cohort_mem block warp 64 t).mp ht
  exact fifth_snapshot_indices p ops input block warp peer s hpeer

theorem normal_wave_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat)
    (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (normalWaveState p ops input block warp s).regs t (18 + 2 * e) =
      some (normalizedValue ops input t (weightBuffer t) (normalScale ops (waveValues ops input block warp 5 lane)) e) := by
  have ready := normal_wave_ready p ops input block warp lane s hl
  simpa only [reductionA, reductionB, Nat.add_sub_cancel_left, waveValues, xorMask] using ready.values e he

theorem normal_wave_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) :
    (normalWaveState p ops input block warp s).memory = s.memory ∧
    (normalWaveState p ops input block warp s).epochs = s.epochs := by
  have nf := normal_fold_preserves ops input (reductionA ops input block warp) (reductionB ops input block warp)
    (cohortThreads block warp 64) (fifthSnapshot p ops input block warp s)
  have sf := fifth_snapshot_preserves p ops input block warp s
  exact ⟨nf.1.trans sf.1, nf.2.trans sf.2.1⟩

theorem normal_wave_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : (normalWaveState p ops input block warp s).trace.length = s.trace.length + 512 := by
  change (normalFold ops input _ _ _ _).trace.length = _
  rw [normal_fold_trace_length, (fifth_snapshot_preserves p ops input block warp s).2.2, prepare_fold_trace_length]
  have len : (cohortThreads block warp 64).length = 64 := by simp [cohortThreads]
  rw [len]

theorem normal_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (normalWaveState p ops input block warp s).trace, Good access := by
  apply normal_fold_good
  have preparedGood := prepare_fold_good ops input (cohortThreads block warp 64) s good
  simpa only [(fifth_snapshot_preserves p ops input block warp s).2.2] using preparedGood

theorem normal_wave_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry p) (normalWaveState p ops input block warp (initial (layout p) input outside)).trace = true :=
  race_free p _ (normal_wave_good p ops input block warp _ (by intro access ha; cases ha))

#print axioms native_normal_fold
#print axioms native_normalization_step
#print axioms normal_wave_ready
#print axioms normal_wave_value
#print axioms normal_wave_preserves
#print axioms normal_wave_trace_length
#print axioms normal_wave_good
#print axioms normal_wave_initial_race_free
end LarkNativeQKNormRope
