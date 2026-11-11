import Lark.NativeSoftmaxMaxLastWave

/-! Actual maximum pass through a native physical wave64: the full clamped
prefix, five source-ordered logical32 down/max stages and two partial stores.
Every lane parks at the first block barrier; the barrier has not resumed.
This is not a complete softmax launch or reference-equivalence theorem. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def firstWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : State α :=
  lastWave p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s))

theorem first_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    WaveReady ops input row warp 0 (maxPrefixFold ops input (cohortThreads row warp 64) s) := by
  intro lane hl
  have h := native_prefix_ready p ops input row warp s reads good lane hl
  have coords := cohort_arithmetic row warp lane hw hl
  exact ⟨h.pc,by simpa only [waveValues,coords.1,coords.2.1] using h.accumulator⟩

theorem first_last_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LastReady row warp (waveValues ops input row warp 4)
      (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s)) := by
  have ready := first_stages_ready p ops input row warp 0 4 _ hw
    (first_prefix_ready p ops input row warp s hw reads good)
  have preserves := first_stages_preserves p ops input row warp 0 4
    (maxPrefixFold ops input (cohortThreads row warp 64) s)
  exact {
    pc := fun lane hl => (ready lane hl).1
    accumulator := fun lane hl => (ready lane hl).2
    indices := by
      intro t ht
      have h := (max_fold_member p ops input _ s (cohort_nodup row warp 64) reads good t ht).indices
      simpa only [MaxNativeIndices,preserves.2.1] using h }

theorem first_wave_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0)
    (reads : Reads p input s) (good : ∀ a ∈ s.trace, Good a) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s =
      some (firstWave p ops input row warp s) := by
  rewrite [show fuel.warp = 7+1 by decide,
    native_prefix_step p guarded ops input row warp 7 s hr hw hp reads good]
  rewrite [first_stages_run p guarded ops input row warp 0 4 3 _ hw (by decide)
    (first_prefix_ready p ops input row warp s hw reads good)]
  exact last_wave_warp p guarded ops row warp 2 _ _ hw (first_last_ready p ops input row warp s hw reads good)

theorem first_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (lane : Nat) (hl : lane < 64) :
    (firstWave p ops input row warp s).pc (cohortBase row warp+lane) = 32 :=
  last_wave_pc p ops row warp _ _ lane hl

theorem first_wave_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp half : Nat) (s : State α) (hw : warp < 16) (hh : half < 2) :
    (firstWave p ops input row warp s).memory ⟨.shared,row,0,warp*2+half⟩ =
      some (waveValues ops input row warp 5 (half*32)) :=
  last_wave_partial p ops row warp half (waveValues ops input row warp 4) _ hw hh

theorem first_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : (firstWave p ops input row warp s).epochs = s.epochs := by
  have last := last_wave_preserves p ops row warp (waveValues ops input row warp 4)
    (firstStages p ops input row warp 0 4 (maxPrefixFold ops input (cohortThreads row warp 64) s))
  exact last.2.trans ((first_stages_preserves p ops input row warp 0 4 _).2.2.1.trans
    (max_fold_frames ops input _ s).2.1)

theorem first_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α)
    (reads : Reads p input s) (he : ∀ t ∈ cohortThreads row warp 64, (s.epochs t).block = 0)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (firstWave p ops input row warp s).trace, Good a := by
  have hp := (max_fold_frames ops input (cohortThreads row warp 64) s).2.1
  have hs := first_stages_preserves p ops input row warp 0 4
    (maxPrefixFold ops input (cohortThreads row warp 64) s)
  apply last_wave_good p ops row warp _ _
  · intro t ht
    exact (congrArg (fun epochs => (epochs t).block) (hs.2.2.1.trans hp)).trans (he t ht)
  · simpa only [hs.2.2.2] using max_fold_good p ops input _ s reads good

theorem first_wave_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (l : Location) (hl : l.space = .global ∨ l.buffer ≠ 0) :
    (firstWave p ops input row warp s).memory l = s.memory l := by
  exact (last_wave_memory_frame p ops row warp (waveValues ops input row warp 4) _ l hl).trans
    ((congrFun (first_stages_preserves p ops input row warp 0 4 _).1 l).trans
      (congrFun (max_fold_frames ops input (cohortThreads row warp 64) s).1 l))

theorem first_wave_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (firstWave p ops input row warp s) := by
  intro offset hb
  rewrite [first_wave_memory_frame p ops input row warp s _ (Or.inl rfl)]
  exact reads offset hb

theorem first_wave_initial (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp (initial (layout p) input outside) =
      some (firstWave p ops input row warp (initial (layout p) input outside)) :=
  first_wave_run p guarded ops input row warp _ hr hw (by intro t ht; rfl)
    (initial_reads p input outside) (by intro a ha; cases ha)

theorem first_wave_initial_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    ∀ a ∈ (firstWave p ops input row warp (initial (layout p) input outside)).trace, Good a :=
  first_wave_good p ops input row warp _ (initial_reads p input outside)
    (by intro t ht; rfl) (by intro a ha; cases ha)

theorem first_wave_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    raceFree (geometry p) (firstWave p ops input row warp (initial (layout p) input outside)).trace = true :=
  race_free p _ (first_wave_initial_good p ops input outside row warp)

#print axioms first_prefix_ready
#print axioms first_last_ready
#print axioms first_wave_run
#print axioms first_wave_pc
#print axioms first_wave_partial
#print axioms first_wave_epochs
#print axioms first_wave_good
#print axioms first_wave_memory_frame
#print axioms first_wave_reads
#print axioms first_wave_initial
#print axioms first_wave_initial_good
#print axioms first_wave_initial_race_free
end LarkNativeSoftmax
