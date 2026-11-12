import Lark.NativeFlashInferRmsNormLastWave

/-! Complete actual native wave64 execution from source entry to the first
block barrier: two read-only rounds, five logical32 snapshot reductions and two
partial stores. This is not yet a block/grid or normalized-output theorem.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def firstWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  lastWave p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s))

theorem first_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (pending : ∀ t ∈ cohortThreads row warp 64, InputReady input (t / 1024) (t % 1024) s)
    (good : ∀ a ∈ s.trace, Good a) :
    WaveReady ops input row warp 0 (prefixFold ops input (cohortThreads row warp 64) s) := by
  intro lane hl
  have h := prefix_fold_member p ops input _ s (cohort_nodup row warp 64)
    (cohort_bound p row warp 64 hr hw (by decide)) pending good _
    ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)
  have coords := cohort_arithmetic row warp lane hw hl
  exact ⟨h.pc, by simpa only [waveValues, coords.1, coords.2.1] using h.accumulator⟩

theorem first_last_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (pending : ∀ t ∈ cohortThreads row warp 64, InputReady input (t / 1024) (t % 1024) s)
    (good : ∀ a ∈ s.trace, Good a) :
    LastReady row warp (waveValues ops input row warp 4)
      (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)) := by
  have ready := first_stages_ready p ops input row warp 0 4 _ hw
    (first_prefix_ready p ops input row warp s hr hw pending good)
  have preserves := first_stages_preserves p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)
  exact {
    pc := fun lane hl => (ready lane hl).1
    accumulator := fun lane hl => (ready lane hl).2
    indices := by
      intro t ht
      have h := (prefix_fold_member p ops input _ s (cohort_nodup row warp 64)
        (cohort_bound p row warp 64 hr hw (by decide)) pending good t ht).indices
      simpa only [NativeIndices, preserves.2.1] using h }

theorem first_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0)
    (pending : ∀ t ∈ cohortThreads row warp 64, InputReady input (t / 1024) (t % 1024) s)
    (good : ∀ a ∈ s.trace, Good a) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp s = some (firstWave p ops input row warp s) := by
  rewrite [show fuel.warp = 7 + 1 by decide, native_prefix_step p ops input row warp 7 s hr hw hp pending good]
  rewrite [first_stages_run p ops input row warp 0 4 3 _ hw (by decide)
    (first_prefix_ready p ops input row warp s hr hw pending good)]
  exact last_wave_warp p ops row warp 2 _ _ hw (first_last_ready p ops input row warp s hr hw pending good)

theorem first_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (lane : Nat) (hl : lane < 64) :
    (firstWave p ops input row warp s).pc (cohortBase row warp + lane) = 31 :=
  last_wave_pc p ops row warp _ _ lane hl

theorem first_wave_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp half : Nat) (s : State α) (hw : warp < 16) (hh : half < 2) :
    (firstWave p ops input row warp s).memory ⟨.shared, row, 0, warp * 2 + half⟩ =
      some (waveValues ops input row warp 5 (half * 32)) :=
  last_wave_partial p ops row warp half (waveValues ops input row warp 4) _ hw hh

theorem first_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : (firstWave p ops input row warp s).epochs = s.epochs := by
  have last := last_wave_preserves p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s))
  exact last.2.trans ((first_stages_preserves p ops input row warp 0 4 _).2.2.1.trans
    (prefix_fold_epochs ops input _ s))

theorem first_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (pending : ∀ t ∈ cohortThreads row warp 64, InputReady input (t / 1024) (t % 1024) s)
    (he : ∀ t ∈ cohortThreads row warp 64, (s.epochs t).block = 0)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (firstWave p ops input row warp s).trace, Good a := by
  have hp := prefix_fold_epochs ops input (cohortThreads row warp 64) s
  have hs := first_stages_preserves p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)
  apply last_wave_good p ops row warp _ _
  · intro t ht
    exact (congrArg (fun epochs => (epochs t).block) (hs.2.2.1.trans hp)).trans (he t ht)
  · simpa only [hs.2.2.2] using prefix_fold_good p ops input _ s (cohort_nodup row warp 64)
      (cohort_bound p row warp 64 hr hw (by decide)) pending good

theorem first_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location) (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  have h1 := last_wave_memory_frame p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (prefixFold ops input (cohortThreads row warp 64) s)) l hl
  have h2 := (first_stages_preserves p ops input row warp 0 4
    (prefixFold ops input (cohortThreads row warp 64) s)).1
  exact h1.trans ((congrFun h2 l).trans (congrFun (prefix_fold_memory ops input _ s) l))

theorem first_wave_inputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp inputRow inputTid : Nat) (s : State α) (ready : InputReady input inputRow inputTid s) :
    InputReady input inputRow inputTid (firstWave p ops input row warp s) := by
  intro j hj
  exact (first_wave_memory_frame p ops input row warp s _ (Or.inl rfl)).trans (ready j hj)

theorem first_wave_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp (initial p input outside) =
      some (firstWave p ops input row warp (initial p input outside)) :=
  first_wave_run p ops input row warp _ hr hw (by intro t ht; rfl)
    (initial_input_ready_lanes p input outside _ (cohort_bound p row warp 64 hr hw (by decide)))
    (by intro a ha; cases ha)

theorem first_wave_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    ∀ a ∈ (firstWave p ops input row warp (initial p input outside)).trace, Good a :=
  first_wave_good p ops input row warp _ hr hw
    (initial_input_ready_lanes p input outside _ (cohort_bound p row warp 64 hr hw (by decide)))
    (by intro t ht; rfl) (by intro a ha; cases ha)

theorem first_wave_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    raceFree (geometry p) (firstWave p ops input row warp (initial p input outside)).trace = true :=
  race_free p _ (first_wave_initial_good p ops input outside row warp hr hw)

#print axioms first_prefix_ready
#print axioms first_last_ready
#print axioms first_wave_run
#print axioms first_wave_pc
#print axioms first_wave_partial
#print axioms first_wave_epochs
#print axioms first_wave_good
#print axioms first_wave_memory_frame
#print axioms first_wave_inputs
#print axioms first_wave_initial
#print axioms first_wave_initial_good
#print axioms first_wave_initial_race_free
end LarkNativeFlashInferRmsNorm
