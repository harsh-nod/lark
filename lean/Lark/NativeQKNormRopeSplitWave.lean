import Lark.NativeQKNormRopeSplitRotaryWave
import Lark.NativeQKNormRopeSplitStores

/-! Complete actual split-half physical-wave execution, including both fences,
four rotary snapshots, all products and all output stores, with pinned fuel. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitWaveState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) : State α :=
  splitStoreFold ops (splitWaveResult ops input block warp) (cohortThreads block warp 64)
    (splitSecondFence p ops input block warp s)

theorem native_split_store_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4) :
    (cohortThreads block warp 64).foldlM
      (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s)
      (splitSecondFence p ops input block warp s) = some (splitWaveState p ops input block warp s) := by
  apply split_store_fold_run p ops _ _ _ (cohort_nodup block warp 64)
    (cohort_bound p block warp 64 hb hw (by decide))
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact split_second_fence_pc p ops input block warp lane s hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact split_rotary_wave_output_index p ops input block warp lane s hl
  · intro t ht e he
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact split_rotary_wave_value p ops input block warp lane e s hl he

theorem split_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) : (splitWaveState p ops input block warp s).pc (cohortBase block warp + lane) = 106 :=
  split_store_fold_pc ops _ _ _ (cohort_nodup block warp 64) _ ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)

theorem native_split_wave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) block warp) fuel.warp s = some (splitWaveState p ops input block warp s) := by
  rw [native_split_second_fence p ops input block warp s hb hw hp hr]
  rw [show (5 : Nat) = 4 + 1 by decide, run_warp_continue, native_split_store_fold p ops input block warp s hb hw]
  change continueCohort p true ops (cohortThreads block warp 64) 4 (splitWaveState p ops input block warp s) = _
  exact continue_at_final_halt p true ops block warp 64 4 _ (by decide)
    (fun lane hl => split_wave_pc p ops input block warp lane s hl)

theorem split_wave_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat)
    (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (splitWaveState p ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (splitWaveResult ops input block warp t e)) :=
  split_store_fold_value ops _ _ _ (cohort_nodup block warp 64) _ e
    ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩) he

theorem split_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (splitWaveState p ops input block warp s) := by
  apply split_store_fold_reads
  change Reads p input (splitRotaryWave p ops input block warp s)
  simpa only [Reads, split_rotary_wave_memory] using hr

theorem split_wave_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    ((splitWaveState p ops input block warp s).epochs t).block = (s.epochs t).block ∧
    ((splitWaveState p ops input block warp s).epochs t).warp = (s.epochs t).warp + 2 := by
  have frame := (split_store_fold_preserves ops (splitWaveResult ops input block warp)
    (cohortThreads block warp 64) (splitSecondFence p ops input block warp s)).2
  change (splitWaveState p ops input block warp s).epochs = (splitSecondFence p ops input block warp s).epochs at frame
  simpa only [frame] using split_second_fence_epoch p ops input block warp lane s hl

theorem split_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (loc : Location) (hn : ∀ t ∈ cohortThreads block warp 64, loc.buffer ≠ 0 ∨ loc.offset / 4 ≠ t) :
    (splitWaveState p ops input block warp s).memory loc = s.memory loc :=
  (split_store_fold_memory_frame ops _ _ _ loc hn).trans (congrFun (split_rotary_wave_memory p ops input block warp s) loc)

theorem split_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp t : Nat)
    (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (splitWaveState p ops input block warp s).pc t = s.pc t ∧
    (splitWaveState p ops input block warp s).indices t = s.indices t ∧
    (splitWaveState p ops input block warp s).regs t = s.regs t ∧
    (splitWaveState p ops input block warp s).epochs t = s.epochs t := by
  have exchange := split_exchanges_other p block warp 0 4 t (splitWaveNormal ops input block warp)
    (splitFirstFence p ops input block warp s) ht
  have preserved := split_exchanges_preserves p block warp 0 4 (splitWaveNormal ops input block warp)
    (splitFirstFence p ops input block warp s)
  have first := split_first_fence_other p ops input block warp t s ht
  have rotation := split_rotary_fold_other ops input (splitWaveValues ops input block warp)
    (splitWavePeers ops input block warp) (cohortThreads block warp 64) t (splitExchanged p ops input block warp s) ht
  have stored := split_store_fold_other ops (splitWaveResult ops input block warp)
    (cohortThreads block warp 64) t (splitSecondFence p ops input block warp s) ht
  have contains : (cohortThreads block warp 64).contains t = false := by simp [ht]
  have pc : (splitRotaryWave p ops input block warp s).pc t = s.pc t := rotation.1.trans (exchange.1.trans first.1)
  have ix : (splitRotaryWave p ops input block warp s).indices t = s.indices t :=
    rotation.2.1.trans ((congrFun preserved.2.1 t).trans first.2.1)
  have rg : (splitRotaryWave p ops input block warp s).regs t = s.regs t :=
    rotation.2.2.trans (exchange.2.trans first.2.2.1)
  have secondPc : (splitSecondFence p ops input block warp s).pc t = s.pc t := by
    simp only [splitSecondFence, resume, contains, Bool.false_eq_true, ↓reduceIte, pc]
  have ep : (splitSecondFence p ops input block warp s).epochs t = s.epochs t := by
    simp only [splitSecondFence, resume, contains, Bool.false_eq_true, ↓reduceIte, split_rotary_wave_epochs]
    exact first.2.2.2
  have storedEpochs := (split_store_fold_preserves ops (splitWaveResult ops input block warp)
    (cohortThreads block warp 64) (splitSecondFence p ops input block warp s)).2
  exact ⟨stored.1.trans secondPc, stored.2.1.trans ix, stored.2.2.trans rg, (congrFun storedEpochs t).trans ep⟩

theorem split_wave_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) (s : State α) :
    (splitWaveState p ops input block warp s).trace.length = s.trace.length + 1280 := by
  have len : (cohortThreads block warp 64).length = 64 := by simp [cohortThreads]
  have stores := split_store_fold_trace_length ops (splitWaveResult ops input block warp)
    (cohortThreads block warp 64) (splitSecondFence p ops input block warp s)
  change (splitWaveState p ops input block warp s).trace.length =
    (splitRotaryWave p ops input block warp s).trace.length + 4 * (cohortThreads block warp 64).length at stores
  have rotation := split_rotary_fold_trace_length ops input (splitWaveValues ops input block warp)
    (splitWavePeers ops input block warp) (cohortThreads block warp 64) (splitExchanged p ops input block warp s)
  change (splitRotaryWave p ops input block warp s).trace.length =
    (splitExchanged p ops input block warp s).trace.length + 8 * (cohortThreads block warp 64).length at rotation
  have prefixTrace := congrArg List.length (split_exchanged_trace p ops input block warp s)
  have normal := normal_wave_trace_length p ops input block warp s
  rw [len] at stores rotation
  omega

theorem split_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (splitWaveState p ops input block warp s).trace, Good a := by
  apply split_store_fold_good
  change ∀ a ∈ (splitRotaryWave p ops input block warp s).trace, Good a
  apply split_rotary_fold_good
  rw [split_exchanged_trace]
  exact normal_wave_good p ops input block warp s good

theorem split_wave_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry p) (splitWaveState p ops input block warp (initial (layout p) input outside)).trace = true :=
  race_free p _ (split_wave_good p ops input block warp _ (by intro a ha; cases ha))

#print axioms native_split_store_fold
#print axioms split_wave_pc
#print axioms native_split_wave
#print axioms split_wave_value
#print axioms split_wave_reads
#print axioms split_wave_epoch
#print axioms split_wave_memory_frame
#print axioms split_wave_other
#print axioms split_wave_trace_length
#print axioms split_wave_good
#print axioms split_wave_initial_race_free
end LarkNativeQKNormRope
