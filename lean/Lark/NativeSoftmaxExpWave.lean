import Lark.NativeSoftmaxSumLastWave

/-! Actual native64 exponentiation/sum wave from the proved maximum phase to
the third block barrier. Both logical32 XOR trees follow the exact source
addition order and write distinct partial sums. The block barrier has not
resumed; serial sum, normalization and whole-launch execution remain open. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : State α :=
  sumLastWave p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s))

theorem exp_wave_last_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    SumLastReady row warp (sumWaveValues ops input row warp 4)
      (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) := by
  have h := sum_stages_ready p ops input row warp 0 4 _ hw
    (sum_scalar_wave_cohort_ready p ops input row warp s hw ready)
  have hf := sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)
  exact {
    pc := fun lane hl => (h lane hl).1
    accumulator := fun lane hl => (h lane hl).2
    indices := by
      intro t ht
      have hi := exp_scalar_fold_native ops input row (cohortThreads row warp 64) s t
        (exp_cohort_row row warp hw) (ready.native t ht)
      simpa only [MaxNativeIndices,hf.2.1] using hi }

theorem exp_wave_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s=some (expWave p ops input row warp s) := by
  rewrite [native_sum_first_four_of_cohort p guarded ops input row warp s hw ready]
  exact sum_last_wave_warp p guarded ops row warp 2 _ _ hw
    (exp_wave_last_ready p ops input row warp s hw ready)

theorem exp_wave_of_maximum (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s=some (expWave p ops input row warp s) :=
  exp_wave_run p guarded ops input row warp s hw (exp_cohort_entry_of_maximum p ops input row warp s hw ready)

theorem exp_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hl : lane<64) :
    (expWave p ops input row warp s).pc (cohortBase row warp+lane)=82 :=
  sum_last_wave_pc p ops row warp _ _ lane hl

theorem exp_wave_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp half : Nat) (s : State α) (hw : warp<16) (hh : half<2) :
    (expWave p ops input row warp s).memory ⟨.shared,row,1,warp*2+half⟩=
      some (sumWaveValues ops input row warp 5 (half*32)) := by
  have h := sum_last_wave_partial p ops row warp half (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) hw hh
  simpa only [sumWaveValues,show sumDistance 4=1 by decide] using h

theorem exp_wave_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : (expWave p ops input row warp s).epochs=s.epochs :=
  (sum_last_wave_preserves p ops row warp (sumWaveValues ops input row warp 4) _).2.trans
    ((sum_stages_preserves p ops input row warp 0 4 _).2.2.1.trans
      (exp_scalar_fold_epochs ops input row (cohortThreads row warp 64) s))

theorem exp_wave_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) :
    (expWave p ops input row warp s).regs (cohortBase row warp+lane) 6=
      some (sumWaveValues ops input row warp 5 lane) := by
  exact sum_last_wave_sum p ops row warp lane (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) hw hl

theorem exp_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    ∀ a ∈ (expWave p ops input row warp s).trace, Good a := by
  apply sum_last_wave_good p ops row warp _ _
  · intro t ht
    have hf := (sum_stages_preserves p ops input row warp 0 4 _).2.2.1.trans
      (exp_scalar_fold_epochs ops input row (cohortThreads row warp 64) s)
    exact (congrArg (fun epochs => (epochs t).block) hf).trans (ready.epoch t ht)
  · have hf := (sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)).2.2.2
    rewrite [hf]
    exact exp_scalar_fold_good p ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw) ready

theorem exp_wave_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    raceFree (geometry p) (expWave p ops input row warp s).trace=true :=
  race_free p _ (exp_wave_good p ops input row warp s hw ready)

theorem initial_exp_wave (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row<p.rows) (hw : warp<16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp
      (maximumState p ops input row (initial (layout p) input outside))=
      some (expWave p ops input row warp (maximumState p ops input row (initial (layout p) input outside))) :=
  exp_wave_of_maximum p guarded ops input row warp _ hw (initial_maximum_ready p ops input outside row hr)

#print axioms exp_wave_last_ready
#print axioms exp_wave_run
#print axioms exp_wave_of_maximum
#print axioms exp_wave_pc
#print axioms exp_wave_partial
#print axioms exp_wave_epochs
#print axioms exp_wave_sum
#print axioms exp_wave_good
#print axioms exp_wave_race_free
#print axioms initial_exp_wave
end LarkNativeSoftmax
