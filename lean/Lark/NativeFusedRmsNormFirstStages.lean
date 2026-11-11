import Lark.NativeFusedRmsNormAdd

/-! Compose the first four actual logical32 XOR/add stages in the unchanged
native scheduler. The fifth shuffle, partial stores and barrier remain explicit.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def xorMask (n : Nat) : Nat := 16 / 2 ^ n

theorem first_shuffle_code (n : Nat) (hn : n < 5) :
    program[23 + 2 * n]? = some (.shuffle .xor 1 0 (.const (xorMask n : Int)) 32) := by
  have table : ∀ k : Fin 5,
      program[23 + 2 * k.val]? = some (.shuffle .xor 1 0 (.const (xorMask k.val : Int)) 32) := by decide
  exact table ⟨n, hn⟩

theorem first_add_code (n : Nat) (hn : n < 5) :
    program[23 + 2 * n + 1]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  have table : ∀ k : Fin 5,
      program[23 + 2 * k.val + 1]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by decide
  exact table ⟨n, hn⟩

theorem xor_mask_bound (n : Nat) (hn : n < 5) : xorMask n < 32 := by
  have table : ∀ k : Fin 5, xorMask k.val < 32 := by decide
  exact table ⟨n, hn⟩

def waveValues (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : Nat → Nat → α
  | 0, lane => threadSum ops input row (warp * 64 + lane)
  | n + 1, lane => ops.add (waveValues ops input row warp n lane)
      (waveValues ops input row warp n (xorPeer32 lane (xorMask n)))

def WaveReady (ops : Ops α) (input : Nat → Nat → α) (row warp n : Nat) (s : State α) : Prop :=
  ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 23 + 2 * n ∧
    s.regs (cohortBase row warp + lane) 0 = some (waveValues ops input row warp n lane)

def firstStages (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => firstStages p ops input row warp (n + 1) remaining
      (xorStep p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s)

theorem first_stage_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hw : warp < 16) (hn : n < 4)
    (ready : WaveReady ops input row warp n s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) s).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (xorStep p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s) := by
  apply xor_step_run p ops row warp 64 (23 + 2 * n) (xorMask n) _ s hw (Or.inr rfl)
    (xor_mask_bound n (by omega)) (fun lane hl => (ready lane hl).1) (fun lane hl => (ready lane hl).2)
    (first_shuffle_code n (by omega)) (first_add_code n (by omega))
  intro u t ht hp
  unfold LarkCollective.parked
  rewrite [hp, show 23 + 2 * n + 2 = 23 + 2 * (n + 1) by omega, first_shuffle_code (n + 1) (by omega)]
  rfl

theorem first_stage_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hw : warp < 16) :
    WaveReady ops input row warp (n + 1)
      (xorStep p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s) := by
  intro lane hl
  have h := xor_step_fields p ops row warp 64 (23 + 2 * n) (xorMask n) lane
    (waveValues ops input row warp n) s hw (by decide) hl
  simpa only [waveValues, show 23 + 2 * n + 2 = 23 + 2 * (n + 1) by omega] using h

theorem continue_shuffle (p : Shape) (ops : Ops α) (ts cohort : List Nat) (n : Nat) (s : State α)
    (hc : LarkPartitionCollective.nextCohort program ts s = some cohort) :
    continueCohort p ops ts n s =
      (LarkPartitionCollective.runShuffle (geometry p) program cohort s).bind
        (fun next => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts n next) := by
  unfold continueCohort
  rewrite [hc]
  rfl

theorem bind_follow (f : Option (State α)) (g h : State α → Option (State α)) (next : State α)
    (hf : f.bind g = some next) : f.bind (fun s => (g s).bind h) = h next := by
  cases f with
  | none => simp at hf
  | some s =>
      simp only [Option.some_bind] at hf ⊢
      rewrite [hf]
      rfl

theorem continue_fold (p : Shape) (ops : Ops α) (ts cohort : List Nat) (n : Nat) (s next : State α)
    (hc : LarkPartitionCollective.nextCohort program ts s = some cohort)
    (hf : ((LarkPartitionCollective.runShuffle (geometry p) program cohort s).bind
      fun shuffled => ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next) :
    continueCohort p ops ts (n + 1) s = continueCohort p ops ts n next := by
  rewrite [continue_shuffle p ops ts cohort (n + 1) s hc]
  have hrun : (fun shuffled => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program ts (n + 1) shuffled) =
      (fun shuffled => (ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled).bind
        (continueCohort p ops ts n)) := by
    funext shuffled; exact run_warp_continue p ops ts n shuffled
  rewrite [hrun]
  exact bind_follow _ _ _ next hf

theorem first_stages_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hw : warp < 16)
    (ready : WaveReady ops input row warp n s) :
    WaveReady ops input row warp (n + remaining) (firstStages p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => simpa only [firstStages, Nat.add_zero] using ready
  | succ remaining ih =>
      have step := first_stage_ready p ops input row warp n s hw
      have final := ih (n + 1) _ step
      simpa only [firstStages, show n + 1 + remaining = n + (remaining + 1) by omega] using final

theorem first_stages_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining extra : Nat) (s : State α) (hw : warp < 16) (hn : n + remaining ≤ 4)
    (ready : WaveReady ops input row warp n s) :
    continueCohort p ops (cohortThreads row warp 64) (extra + remaining) s =
      continueCohort p ops (cohortThreads row warp 64) extra (firstStages p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      have hcohort : LarkPartitionCollective.nextCohort program (cohortThreads row warp 64) s =
          some (cohortThreads row warp 64) := by
        apply cohort_next row warp 64 (23 + 2 * n) s (by decide) (fun lane hl => (ready lane hl).1)
        intro t ht
        simp only [LarkPartitionCollective.isShuffle, ht, first_shuffle_code n (by omega)]
      rewrite [show extra + (remaining + 1) = (extra + remaining) + 1 by omega,
        continue_fold p ops _ _ (extra + remaining) s _ hcohort (first_stage_run p ops input row warp n s hw (by omega) ready)]
      exact ih (n + 1) _ (by omega) (first_stage_ready p ops input row warp n s hw)

theorem first_stages_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) :
    (firstStages p ops input row warp n remaining s).memory = s.memory ∧
    (firstStages p ops input row warp n remaining s).indices = s.indices ∧
    (firstStages p ops input row warp n remaining s).epochs = s.epochs ∧
    (firstStages p ops input row warp n remaining s).trace = s.trace := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (xorStep p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s)
      have step := xor_step_preserves p ops row warp 64 (23 + 2 * n) (xorMask n) (waveValues ops input row warp n) s
      exact ⟨h.1.trans step.1, h.2.1.trans step.2.1, h.2.2.1.trans step.2.2.1, h.2.2.2.trans step.2.2.2⟩

theorem native_first_four (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp (initial p input outside) =
      continueCohort p ops (cohortThreads row warp 64) 3
        (firstStages p ops input row warp 0 4
          (prefixFold ops input (cohortThreads row warp 64) (initial p input outside))) := by
  have ready : WaveReady ops input row warp 0
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) := by
    intro lane hl
    have h := native_prefix_ready p ops input outside row warp hr hw lane hl
    have coords := cohort_arithmetic row warp lane hw hl
    exact ⟨h.pc, by simpa only [waveValues, coords.1, coords.2.1] using h.accumulator⟩
  rewrite [show fuel.warp = 7 + 1 by decide, native_prefix_initial p ops input outside row warp 7 hr hw]
  exact first_stages_run p ops input row warp 0 4 3 _ hw (by decide) ready

#print axioms first_shuffle_code
#print axioms first_add_code
#print axioms first_stage_run
#print axioms first_stage_ready
#print axioms continue_fold
#print axioms first_stages_ready
#print axioms first_stages_run
#print axioms first_stages_preserves
#print axioms native_first_four
end LarkNativeFusedRmsNorm
