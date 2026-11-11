import Lark.NativeFusedRmsNormMixed

/-! Source-ordered block reduction through the first four XOR/add stages.
The actual physical64 lane fold includes its parked upper32 suffix every time.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem second_shuffle_code (n : Nat) (hn : n < 5) :
    program[38 + 2 * n]? = some (.shuffle .xor 1 0 (.const (xorMask n : Int)) 32) := by
  have table : ∀ k : Fin 5,
      program[38 + 2 * k.val]? = some (.shuffle .xor 1 0 (.const (xorMask k.val : Int)) 32) := by decide
  exact table ⟨n, hn⟩

theorem second_add_code (n : Nat) (hn : n < 5) :
    program[38 + 2 * n + 1]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  have table : ∀ k : Fin 5,
      program[38 + 2 * k.val + 1]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by decide
  exact table ⟨n, hn⟩

def logicalValues (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : Nat → Nat → α
  | 0, lane => blockPartial ops input row lane
  | n + 1, lane => ops.add (logicalValues ops input row n lane)
      (logicalValues ops input row n (xorPeer32 lane (xorMask n)))

def blockSum (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : α := logicalValues ops input row 5 0

def logicalStages (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => logicalStages p ops input row (n + 1) remaining
      (xorStep p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s)

theorem upper_not_active (row tid : Nat) (hl : 32 ≤ tid) :
    cohortBase row 0 + tid ∉ cohortThreads row 0 32 := by
  intro ht
  obtain ⟨peer, hp, he⟩ := (cohort_mem row 0 32 _).mp ht
  omega

theorem logical_stage_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (ready : MixedReady row (38 + 2 * n) (logicalValues ops input row n) s) :
    MixedReady row (38 + 2 * (n + 1)) (logicalValues ops input row (n + 1))
      (xorStep p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s) := by
  exact {
    active := {
      pc := by
        intro lane hl
        have h := (xor_step_fields p ops row 0 32 (38 + 2 * n) (xorMask n) lane
          (logicalValues ops input row n) s (by decide) (by decide) hl).1
        simpa only [show 38 + 2 * n + 2 = 38 + 2 * (n + 1) by omega] using h
      accumulator := by
        intro lane hl
        exact (xor_step_fields p ops row 0 32 (38 + 2 * n) (xorMask n) lane
          (logicalValues ops input row n) s (by decide) (by decide) hl).2 }
    inactive := by
      intro tid hl hu
      exact (xor_step_other p ops row 0 32 (38 + 2 * n) (xorMask n) (cohortBase row 0 + tid)
        (logicalValues ops input row n) s (upper_not_active row tid hl)).1.trans (ready.inactive tid hl hu) }

theorem logical_stage_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (hn : n < 4)
    (ready : MixedReady row (38 + 2 * n) (logicalValues ops input row n) s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 32) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (xorStep p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s) := by
  apply shuffle_physical_fold p ops row s _
  · apply xor_step_run p ops row 0 32 (38 + 2 * n) (xorMask n) _ s (by decide) (Or.inl rfl)
      (xor_mask_bound n (by omega)) ready.active.pc ready.active.accumulator
      (second_shuffle_code n (by omega)) (second_add_code n (by omega))
    intro u t ht hp
    unfold LarkCollective.parked
    rewrite [hp, show 38 + 2 * n + 2 = 38 + 2 * (n + 1) by omega, second_shuffle_code (n + 1) (by omega)]
    rfl
  · exact (logical_stage_ready p ops input row n s ready).inactive

theorem logical_stages_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α)
    (ready : MixedReady row (38 + 2 * n) (logicalValues ops input row n) s) :
    MixedReady row (38 + 2 * (n + remaining)) (logicalValues ops input row (n + remaining))
      (logicalStages p ops input row n remaining s) := by
  induction remaining generalizing n s with
  | zero => simpa only [logicalStages, Nat.add_zero] using ready
  | succ remaining ih =>
      have step := logical_stage_ready p ops input row n s ready
      have done := ih (n + 1) _ step
      simpa only [logicalStages, show n + 1 + remaining = n + (remaining + 1) by omega] using done

theorem logical_stages_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining extra : Nat) (s : State α) (hn : n + remaining ≤ 4)
    (ready : MixedReady row (38 + 2 * n) (logicalValues ops input row n) s) :
    continueCohort p ops (cohortThreads row 0 64) (extra + remaining) s =
      continueCohort p ops (cohortThreads row 0 64) extra (logicalStages p ops input row n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      have hc := mixed_next row (38 + 2 * n) (logicalValues ops input row n) s ready .xor 1 0 _
        (second_shuffle_code n (by omega))
      rewrite [show extra + (remaining + 1) = (extra + remaining) + 1 by omega,
        continue_fold p ops _ _ (extra + remaining) s _ hc (logical_stage_run p ops input row n s (by omega) ready)]
      exact ih (n + 1) _ (by omega) (logical_stage_ready p ops input row n s ready)

theorem logical_stages_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α) :
    (logicalStages p ops input row n remaining s).memory = s.memory ∧
    (logicalStages p ops input row n remaining s).indices = s.indices ∧
    (logicalStages p ops input row n remaining s).epochs = s.epochs ∧
    (logicalStages p ops input row n remaining s).trace = s.trace := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (xorStep p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s)
      have step := xor_step_preserves p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s
      exact ⟨h.1.trans step.1, h.2.1.trans step.2.1, h.2.2.1.trans step.2.2.1, h.2.2.2.trans step.2.2.2⟩

theorem logical_stages_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row 0 32) :
    (logicalStages p ops input row n remaining s).pc t = s.pc t ∧
    (logicalStages p ops input row n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (xorStep p ops row 0 32 (38 + 2 * n) (xorMask n) (logicalValues ops input row n) s)
      have step := xor_step_other p ops row 0 32 (38 + 2 * n) (xorMask n) t (logicalValues ops input row n) s ht
      exact ⟨h.1.trans step.1, h.2.trans step.2⟩

#print axioms second_shuffle_code
#print axioms second_add_code
#print axioms logical_stage_ready
#print axioms logical_stage_run
#print axioms logical_stages_ready
#print axioms logical_stages_run
#print axioms logical_stages_preserves
#print axioms logical_stages_other
end LarkNativeFusedRmsNorm
