import Lark.NativeQKNormRopeSplitFold

/-! Actual physical split-half wave from normalization through both source
warp fences and all four rotary groups. Every exchange is a real snapshot. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitWaveValues (ops : Ops α) (input : Nat → Nat → α) (block warp t e : Nat) : α :=
  splitWaveNormal ops input block warp (t - cohortBase block warp) e
def splitWavePeers (ops : Ops α) (input : Nat → Nat → α) (block warp t e : Nat) : α :=
  splitWaveNormal ops input block warp (xorPeer32 (t - cohortBase block warp) 16) e
def splitWaveResult (ops : Ops α) (input : Nat → Nat → α) (block warp t e : Nat) : α :=
  splitLaneResult ops input (splitWaveValues ops input block warp t) (splitWavePeers ops input block warp t) t e

theorem split_exchanged_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) :
    (splitExchanged p ops input block warp s).memory = s.memory :=
  (split_exchanges_preserves p block warp 0 4 (splitWaveNormal ops input block warp) _).1.trans
    (normal_wave_preserves p ops input block warp s).1

theorem split_exchanged_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) : NativeIndices (cohortBase block warp + lane) (splitExchanged p ops input block warp s) := by
  have frame := (split_exchanges_preserves p block warp 0 4 (splitWaveNormal ops input block warp)
    (splitFirstFence p ops input block warp s)).2.1
  simpa only [NativeIndices, frame] using split_first_fence_indices p ops input block warp lane s hl

theorem split_exchanged_trace (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) :
    (splitExchanged p ops input block warp s).trace = (normalWaveState p ops input block warp s).trace :=
  (split_exchanges_preserves p block warp 0 4 (splitWaveNormal ops input block warp) _).2.2.2

def splitRotaryWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) : State α :=
  splitRotaryFold ops input (splitWaveValues ops input block warp) (splitWavePeers ops input block warp)
    (cohortThreads block warp 64) (splitExchanged p ops input block warp s)

theorem native_split_rotary_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4) (hr : Reads p input s) :
    (cohortThreads block warp 64).foldlM
      (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s)
      (splitExchanged p ops input block warp s) = some (splitRotaryWave p ops input block warp s) := by
  apply split_rotary_fold_run p ops input _ _ _ _ (cohort_nodup block warp 64)
    (cohort_bound p block warp 64 hb hw (by decide))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact (split_exchanged_ready p ops input block warp s hw lane hl).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    have ready := (split_exchanged_ready p ops input block warp s hw lane hl).2
    simpa only [SplitRotaryInputs, splitWaveValues, splitWavePeers, Nat.add_sub_cancel_left] using ready
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact split_exchanged_indices p ops input block warp lane s hl
  · simpa only [Reads, split_exchanged_memory] using hr

theorem split_rotary_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    (splitRotaryWave p ops input block warp s).pc (cohortBase block warp + lane) = 97 :=
  split_rotary_fold_pc ops input _ _ _ _ (cohort_nodup block warp 64) _
    ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)

theorem split_rotary_wave_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat)
    (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (splitRotaryWave p ops input block warp s).regs t (33 + 5 * e) = some (splitWaveResult ops input block warp t e) :=
  split_rotary_fold_value ops input _ _ _ _ (cohort_nodup block warp 64) _ e
    ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩) he

theorem split_rotary_wave_output_index (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    (splitRotaryWave p ops input block warp s).indices t 6 = some ((outputAddress t 0 : Nat) : Int) :=
  (split_rotary_fold_index ops input _ _ _ _ 6 _ (by decide)).trans
    (split_exchanged_indices p ops input block warp lane s hl).2.2.2.2.2

theorem split_rotary_wave_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) :
    (splitRotaryWave p ops input block warp s).memory = s.memory :=
  (split_rotary_fold_preserves ops input _ _ _ _).1.trans (split_exchanged_memory p ops input block warp s)

theorem split_rotary_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) :
    (splitRotaryWave p ops input block warp s).epochs = (splitFirstFence p ops input block warp s).epochs :=
  (split_rotary_fold_preserves ops input (splitWaveValues ops input block warp)
    (splitWavePeers ops input block warp) (cohortThreads block warp 64) (splitExchanged p ops input block warp s)).2.trans
    (split_exchanges_preserves p block warp 0 4 (splitWaveNormal ops input block warp)
      (splitFirstFence p ops input block warp s)).2.2.1

def splitSecondFence (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) : State α :=
  resume (cohortThreads block warp 64) .warp (splitRotaryWave p ops input block warp s)

theorem split_second_fence_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    (splitSecondFence p ops input block warp s).pc (cohortBase block warp + lane) = 98 := by
  have contains : (cohortThreads block warp 64).contains (cohortBase block warp + lane) = true :=
    List.contains_iff_mem.mpr ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)
  simp only [splitSecondFence, resume, contains, ↓reduceIte, split_rotary_wave_pc p ops input block warp lane s hl]

theorem split_second_fence_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    ((splitSecondFence p ops input block warp s).epochs t).block = (s.epochs t).block ∧
    ((splitSecondFence p ops input block warp s).epochs t).warp = (s.epochs t).warp + 2 := by
  have contains : (cohortThreads block warp 64).contains (cohortBase block warp + lane) = true :=
    List.contains_iff_mem.mpr ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)
  have first := split_first_fence_epoch p ops input block warp lane s hl
  simp only [splitSecondFence, resume, contains, ↓reduceIte, bumpEpoch, split_rotary_wave_epochs]
  exact ⟨first.1, by omega⟩

theorem native_split_second_fence (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) block warp) fuel.warp s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp 64) 5 (splitSecondFence p ops input block warp s) := by
  rw [native_split_exchanges p ops input block warp s hb hw hp hr]
  rw [show (6 : Nat) = 5 + 1 by decide, run_warp_continue, native_split_rotary_fold p ops input block warp s hb hw hr]
  change continueCohort p true ops (cohortThreads block warp 64) 5 (splitRotaryWave p ops input block warp s) = _
  exact continue_at_split_fence p ops block warp 64 97 5 _ (by decide)
    (split_barrier_code 97 (Or.inr rfl)) (fun lane hl => split_rotary_wave_pc p ops input block warp lane s hl)

#print axioms split_exchanged_memory
#print axioms split_exchanged_indices
#print axioms split_exchanged_trace
#print axioms native_split_rotary_fold
#print axioms split_rotary_wave_pc
#print axioms split_rotary_wave_value
#print axioms split_rotary_wave_output_index
#print axioms split_rotary_wave_memory
#print axioms split_rotary_wave_epochs
#print axioms split_second_fence_pc
#print axioms split_second_fence_epoch
#print axioms native_split_second_fence
end LarkNativeQKNormRope
