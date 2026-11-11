import Lark.NativeSoftmaxSumCombine

/-! Compose the first four actual logical32 XOR/sum stages in the unchanged
native scheduler. The fifth shuffle, partial stores and barrier remain explicit.
-/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumDistance (n : Nat) : Nat := 16 / 2 ^ n

theorem sum_shuffle_code (guarded : Bool) (n : Nat) (hn : n < 5) :
    (program guarded)[70 + 2 * n]? = some (.shuffle .xor 9 6 (.const (sumDistance n : Int)) 32) := by
  have table : ∀ k : Fin 5,
      (program guarded)[70 + 2 * k.val]? = some (.shuffle .xor 9 6 (.const (sumDistance k.val : Int)) 32) := by cases guarded <;> decide
  exact table ⟨n, hn⟩

theorem sum_combine_code (guarded : Bool) (n : Nat) (hn : n < 5) :
    (program guarded)[70 + 2 * n + 1]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9)))) := by
  have table : ∀ k : Fin 5,
      (program guarded)[70 + 2 * k.val + 1]? = some (.scalar (.assign 6 (.bin .add (.reg 6) (.reg 9)))) := by cases guarded <;> decide
  exact table ⟨n, hn⟩

theorem sum_distance_bound (n : Nat) (hn : n < 5) : sumDistance n < 32 := by
  have table : ∀ k : Fin 5, sumDistance k.val < 32 := by decide
  exact table ⟨n, hn⟩

def sumWaveValues (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : Nat → Nat → α
  | 0, lane => threadExpSum ops input row (warp * 64 + lane)
  | n + 1, lane => ops.add (sumWaveValues ops input row warp n lane)
      (sumWaveValues ops input row warp n (sumXorPeer32 lane (sumDistance n)))

def SumWaveReady (ops : Ops α) (input : Nat → Nat → α) (row warp n : Nat) (s : State α) : Prop :=
  ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 70 + 2 * n ∧
    s.regs (cohortBase row warp + lane) 6 = some (sumWaveValues ops input row warp n lane)

def sumStages (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => sumStages p ops input row warp (n + 1) remaining
      (sumXorStep p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s)

theorem sum_stage_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hw : warp < 16) (hn : n < 4)
    (ready : SumWaveReady ops input row warp n s) :
    ((LarkPartitionCollective.runShuffle (geometry p) (program guarded) (cohortThreads row warp 64) s).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane u) shuffled) =
      some (sumXorStep p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s) := by
  apply sum_xor_step_run p guarded ops row warp 64 (70 + 2 * n) (sumDistance n) _ s hw (Or.inr rfl)
    (sum_distance_bound n (by omega)) (fun lane hl => (ready lane hl).1) (fun lane hl => (ready lane hl).2)
    (sum_shuffle_code guarded n (by omega)) (sum_combine_code guarded n (by omega))
  intro u t ht hp
  unfold LarkCollective.parked
  rewrite [hp, show 70 + 2 * n + 2 = 70 + 2 * (n + 1) by omega, sum_shuffle_code guarded (n + 1) (by omega)]
  rfl

theorem sum_stage_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hw : warp < 16) :
    SumWaveReady ops input row warp (n + 1)
      (sumXorStep p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s) := by
  intro lane hl
  have h := sum_xor_step_fields p ops row warp 64 (70 + 2 * n) (sumDistance n) lane
    (sumWaveValues ops input row warp n) s hw (by decide) hl
  simpa only [sumWaveValues, show 70 + 2 * n + 2 = 70 + 2 * (n + 1) by omega] using h

theorem sum_stages_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hw : warp < 16)
    (ready : SumWaveReady ops input row warp n s) :
    SumWaveReady ops input row warp (n + remaining) (sumStages p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => simpa only [sumStages, Nat.add_zero] using ready
  | succ remaining ih =>
      have step := sum_stage_ready p ops input row warp n s hw
      have final := ih (n + 1) _ step
      simpa only [sumStages, show n + 1 + remaining = n + (remaining + 1) by omega] using final

theorem sum_stages_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining extra : Nat) (s : State α) (hw : warp < 16) (hn : n + remaining ≤ 4)
    (ready : SumWaveReady ops input row warp n s) :
    continueCohort p guarded ops (cohortThreads row warp 64) (extra + remaining) s =
      continueCohort p guarded ops (cohortThreads row warp 64) extra (sumStages p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      have hcohort : LarkPartitionCollective.nextCohort (program guarded) (cohortThreads row warp 64) s =
          some (cohortThreads row warp 64) := by
        apply cohort_next guarded row warp 64 (70 + 2 * n) s (by decide) (fun lane hl => (ready lane hl).1)
        intro t ht
        simp only [LarkPartitionCollective.isShuffle, ht, sum_shuffle_code guarded n (by omega)]
      rewrite [show extra + (remaining + 1) = (extra + remaining) + 1 by omega,
        continue_fold p guarded ops _ _ (extra + remaining) s _ hcohort (sum_stage_run p guarded ops input row warp n s hw (by omega) ready)]
      exact ih (n + 1) _ (by omega) (sum_stage_ready p ops input row warp n s hw)

theorem sum_stages_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) :
    (sumStages p ops input row warp n remaining s).memory = s.memory ∧
    (sumStages p ops input row warp n remaining s).indices = s.indices ∧
    (sumStages p ops input row warp n remaining s).epochs = s.epochs ∧
    (sumStages p ops input row warp n remaining s).trace = s.trace := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (sumXorStep p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s)
      have step := sum_xor_step_preserves p ops row warp 64 (70 + 2 * n) (sumDistance n) (sumWaveValues ops input row warp n) s
      exact ⟨h.1.trans step.1, h.2.1.trans step.2.1, h.2.2.1.trans step.2.2.1, h.2.2.2.trans step.2.2.2⟩

theorem sum_scalar_wave_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    SumWaveReady ops input row warp 0 (expScalarWave ops input row warp s) := by
  intro lane hl
  exact ⟨exp_scalar_wave_pc ops input row warp lane s hw hl,
    exp_scalar_wave_sum p ops input row warp lane s hw hl ready⟩

theorem native_sum_first_four (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s =
      continueCohort p guarded ops (cohortThreads row warp 64) 3
        (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) := by
  rewrite [show fuel.warp=7+1 by decide, run_warp_continue p guarded ops _ 7 s,
    exp_scalar_wave_run p guarded ops input row warp s hw ready]
  simp only [Option.some_bind]
  rewrite [cohort_native_threads p row warp hw]
  exact sum_stages_run p guarded ops input row warp 0 4 3 _ hw (by decide)
    (sum_scalar_wave_ready p ops input row warp s hw ready)

theorem sum_scalar_wave_cohort_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    SumWaveReady ops input row warp 0 (expScalarWave ops input row warp s) := by
  intro lane hl
  refine ⟨exp_scalar_wave_pc ops input row warp lane s hw hl, ?_⟩
  have h := exp_scalar_fold_member_sum p ops input row _ s (cohort_nodup row warp 64)
    (exp_cohort_row row warp hw) ready _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)
  simpa only [sumWaveValues,(cohort_arithmetic row warp lane hw hl).2.1] using h

theorem native_sum_first_four_of_cohort (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (ready : ExpCohortEntry p ops input row (cohortThreads row warp 64) s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s =
      continueCohort p guarded ops (cohortThreads row warp 64) 3
        (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) := by
  rewrite [cohort_native_threads p row warp hw,show fuel.warp=7+1 by decide,
    run_warp_continue p guarded ops _ 7 s,
    exp_scalar_fold_run p guarded ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw) ready]
  simp only [Option.some_bind]
  exact sum_stages_run p guarded ops input row warp 0 4 3 _ hw (by decide)
    (sum_scalar_wave_cohort_ready p ops input row warp s hw ready)

#print axioms sum_scalar_wave_cohort_ready
#print axioms native_sum_first_four_of_cohort
#print axioms sum_shuffle_code
#print axioms sum_combine_code
#print axioms sum_distance_bound
#print axioms sum_stage_run
#print axioms sum_stage_ready
#print axioms sum_stages_ready
#print axioms sum_stages_run
#print axioms sum_stages_preserves
#print axioms sum_scalar_wave_ready
#print axioms native_sum_first_four
end LarkNativeSoftmax
