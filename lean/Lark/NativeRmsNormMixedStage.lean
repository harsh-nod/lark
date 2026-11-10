import Lark.NativeRmsNormMixed

/-! Actual intermediate logical-16 stages inside the unchanged physical wave64.
The inactive suffix is visited and remains parked at the real block barrier.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def logicalValues (ops : Ops α) (input : Nat → Nat → α) (row n : Nat) : Nat → α :=
  LarkDownReduction.reduced ops.add 16 16 (warpSum ops input row) n

theorem inactive_not_active (row tid : Nat) (ht : 16 ≤ tid) :
    cohortBase row 0 + tid ∉ cohortThreads row 0 16 := by
  intro hm
  obtain ⟨lane, hl, he⟩ := (cohort_mem row 0 16 _).mp hm
  omega

theorem mixed_step_inactive (p : Shape) (ops : Ops α) (row pc distance tid : Nat) (values : Nat → α)
    (s : State α) (ht : 16 ≤ tid) (hp : s.pc (cohortBase row 0 + tid) = 55) :
    (cohortStep p ops row 0 16 pc distance 16 values s).pc (cohortBase row 0 + tid) = 55 :=
  (cohort_step_other p ops row 0 16 pc distance 16 (cohortBase row 0 + tid) values s (inactive_not_active row tid ht)).1.trans hp

/-- Source shuffle and subsequent full physical lane fold, for intermediate
logical stages; no inactive lanes are padded into the snapshot operation. -/
theorem mixed_stage_run (p : Shape) (ops : Ops α) (row n : Nat) (values : Nat → α)
    (s : State α) (hn : n < 3) (ready : MixedReady p row (41 + 3 * n) values s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 values s) := by
  apply shuffle_physical_fold p ops row s _ (final_stage_run p ops row n values s hn ready.active)
  intro tid hl hu
  exact mixed_step_inactive p ops row (41 + 3 * n) (2 ^ n) tid values s hl (ready.inactive tid hl hu)

theorem mixed_step_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row n : Nat)
    (s : State α) (ready : MixedReady p row (41 + 3 * n) (logicalValues ops input row n) s) :
    MixedReady p row (41 + 3 * (n + 1)) (logicalValues ops input row (n + 1))
      (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s) := by
  have hr := cohort_step_ready p ops row 0 16 (41 + 3 * n) 16 n (.const 16)
    (warpSum ops input row) s (by decide) (by decide) ready.active
  constructor
  · exact ready_pc_eq p row 0 16 (41 + 3 * n + 3) (41 + 3 * (n + 1)) 16 (.const 16) _ _ (by omega) hr
  · intro tid hl hu
    exact mixed_step_inactive p ops row (41 + 3 * n) (2 ^ n) tid (logicalValues ops input row n) s hl (ready.inactive tid hl hu)

#print axioms mixed_stage_run
#print axioms mixed_step_ready
end LarkNativeRmsNorm
