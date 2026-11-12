import Lark.NativeQKNormRopeAdd

/-! The actual first four logical32 XOR/add stages. The final shuffle and
normalization continuation remain explicit, preserving every source operand. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def xorMask (n : Nat) : Nat := 16 / 2 ^ n

theorem first_shuffle_code (neox : Bool) (n : Nat) (hn : n < 5) :
    (program neox)[24 + 2 * n]? = some (.shuffle .xor 9 4 (.const (xorMask n : Int)) 32) := by
  have table : ∀ flag : Bool, ∀ k : Fin 5,
      (program flag)[24 + 2 * k.val]? = some (.shuffle .xor 9 4 (.const (xorMask k.val : Int)) 32) := by decide
  exact table neox ⟨n, hn⟩

theorem first_add_code (neox : Bool) (n : Nat) (hn : n < 5) :
    (program neox)[24 + 2 * n + 1]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9)))) := by
  have table : ∀ flag : Bool, ∀ k : Fin 5,
      (program flag)[24 + 2 * k.val + 1]? = some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg 9)))) := by decide
  exact table neox ⟨n, hn⟩

theorem xor_mask_bound (n : Nat) (hn : n < 5) : xorMask n < 32 := by
  have table : ∀ k : Fin 5, xorMask k.val < 32 := by decide
  exact table ⟨n, hn⟩

def waveValues (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) : Nat → Nat → α
  | 0, lane => squarePrefix ops input (cohortBase block warp + lane) 4
  | n + 1, lane => ops.add (waveValues ops input block warp n lane)
      (waveValues ops input block warp n (xorPeer32 lane (xorMask n)))

def WaveReady (ops : Ops α) (input : Nat → Nat → α) (block warp n : Nat) (s : State α) : Prop :=
  ∀ lane, lane < 64 → s.pc (cohortBase block warp + lane) = 24 + 2 * n ∧
    s.regs (cohortBase block warp + lane) 4 = some (waveValues ops input block warp n lane)

def firstStages (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => firstStages p ops input block warp (n + 1) remaining
      (xorStep p ops block warp 64 (24 + 2 * n) (xorMask n) (waveValues ops input block warp n) s)

theorem first_stage_run (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n : Nat) (s : State α) (hw : warp < 4) (hn : n < 4)
    (ready : WaveReady ops input block warp n s) :
    ((LarkPartitionCollective.runShuffle (geometry p) (program neox) (cohortThreads block warp 64) s).bind
      fun shuffled => (cohortThreads block warp 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane u) shuffled) =
      some (xorStep p ops block warp 64 (24 + 2 * n) (xorMask n) (waveValues ops input block warp n) s) := by
  apply xor_step_run p neox ops block warp 64 (24 + 2 * n) (xorMask n) _ s hw (Or.inr rfl)
    (xor_mask_bound n (by omega)) (fun lane hl => (ready lane hl).1) (fun lane hl => (ready lane hl).2)
    (first_shuffle_code neox n (by omega)) (first_add_code neox n (by omega))
  intro u t ht hp
  unfold LarkCollective.parked
  rw [hp, show 24 + 2 * n + 2 = 24 + 2 * (n + 1) by omega, first_shuffle_code neox (n + 1) (by omega)]

theorem first_stage_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n : Nat) (s : State α) (hw : warp < 4) :
    WaveReady ops input block warp (n + 1)
      (xorStep p ops block warp 64 (24 + 2 * n) (xorMask n) (waveValues ops input block warp n) s) := by
  intro lane hl
  have h := xor_step_fields p ops block warp 64 (24 + 2 * n) (xorMask n) lane
    (waveValues ops input block warp n) s hw (by decide) hl
  simpa only [waveValues, show 24 + 2 * n + 2 = 24 + 2 * (n + 1) by omega] using h

theorem continue_shuffle (p : Shape) (neox : Bool) (ops : Ops α) (ts cohort : List Nat)
    (n : Nat) (s : State α) (hc : LarkPartitionCollective.nextCohort (program neox) ts s = some cohort) :
    continueCohort p neox ops ts n s =
      (LarkPartitionCollective.runShuffle (geometry p) (program neox) cohort s).bind
        (fun next => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox) ts n next) := by
  unfold continueCohort
  rw [hc]
  rfl

theorem bind_follow (f : Option (State α)) (g h : State α → Option (State α)) (next : State α)
    (hf : f.bind g = some next) : f.bind (fun s => (g s).bind h) = h next := by
  cases f with
  | none => simp at hf
  | some s => simp only [Option.some_bind] at hf ⊢; rw [hf]; rfl

theorem continue_fold (p : Shape) (neox : Bool) (ops : Ops α) (ts cohort : List Nat)
    (n : Nat) (s next : State α) (hc : LarkPartitionCollective.nextCohort (program neox) ts s = some cohort)
    (hf : ((LarkPartitionCollective.runShuffle (geometry p) (program neox) cohort s).bind
      fun shuffled => ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane u) shuffled) = some next) :
    continueCohort p neox ops ts (n + 1) s = continueCohort p neox ops ts n next := by
  rw [continue_shuffle p neox ops ts cohort (n + 1) s hc]
  have hrun : (fun shuffled => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox) ts (n + 1) shuffled) =
      (fun shuffled => (ts.foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane u) shuffled).bind
        (continueCohort p neox ops ts n)) := by
    funext shuffled; exact run_warp_continue p neox ops ts n shuffled
  rw [hrun]
  exact bind_follow _ _ _ next hf

theorem first_stages_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n remaining : Nat) (s : State α) (hw : warp < 4)
    (ready : WaveReady ops input block warp n s) :
    WaveReady ops input block warp (n + remaining) (firstStages p ops input block warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => simpa only [firstStages, Nat.add_zero] using ready
  | succ remaining ih =>
      have step := first_stage_ready p ops input block warp n s hw
      have final := ih (n + 1) _ step
      simpa only [firstStages, show n + 1 + remaining = n + (remaining + 1) by omega] using final

theorem first_stages_run (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n remaining extra : Nat) (s : State α) (hw : warp < 4) (hn : n + remaining ≤ 4)
    (ready : WaveReady ops input block warp n s) :
    continueCohort p neox ops (cohortThreads block warp 64) (extra + remaining) s =
      continueCohort p neox ops (cohortThreads block warp 64) extra (firstStages p ops input block warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      have hcohort : LarkPartitionCollective.nextCohort (program neox) (cohortThreads block warp 64) s =
          some (cohortThreads block warp 64) := by
        apply cohort_next neox block warp 64 (24 + 2 * n) s (by decide) (fun lane hl => (ready lane hl).1)
        intro t ht
        simp only [LarkPartitionCollective.isShuffle, ht, first_shuffle_code neox n (by omega)]
      rw [show extra + (remaining + 1) = (extra + remaining) + 1 by omega,
        continue_fold p neox ops _ _ (extra + remaining) s _ hcohort (first_stage_run p neox ops input block warp n s hw (by omega) ready)]
      exact ih (n + 1) _ (by omega) (first_stage_ready p ops input block warp n s hw)

theorem first_stages_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n remaining : Nat) (s : State α) :
    (firstStages p ops input block warp n remaining s).memory = s.memory ∧
    (firstStages p ops input block warp n remaining s).indices = s.indices ∧
    (firstStages p ops input block warp n remaining s).epochs = s.epochs ∧
    (firstStages p ops input block warp n remaining s).trace = s.trace := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (n + 1) (xorStep p ops block warp 64 (24 + 2 * n) (xorMask n) (waveValues ops input block warp n) s)
      have step := xor_step_preserves p ops block warp 64 (24 + 2 * n) (xorMask n) (waveValues ops input block warp n) s
      exact ⟨h.1.trans step.1, h.2.1.trans step.2.1, h.2.2.1.trans step.2.2.1, h.2.2.2.trans step.2.2.2⟩

theorem first_stages_input_reg (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n remaining t r : Nat) (s : State α) (hr : r < 4) :
    (firstStages p ops input block warp n remaining s).regs t r = s.regs t r := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (n + 1) _).trans (xor_step_input_reg p ops block warp 64 (24 + 2 * n) (xorMask n) t r _ s hr)

theorem native_first_four (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) (hb : block < p.rows * 5) (hw : warp < 4) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
      (warpThreads (geometry p) block warp) fuel.warp (initial (layout p) input outside) =
      continueCohort p neox ops (cohortThreads block warp 64) 11
        (firstStages p ops input block warp 0 4
          (prepareFold ops input (cohortThreads block warp 64) (initial (layout p) input outside))) := by
  have ready : WaveReady ops input block warp 0
      (prepareFold ops input (cohortThreads block warp 64) (initial (layout p) input outside)) := by
    intro lane hl
    have h := native_prepare_ready ops input block warp lane (initial (layout p) input outside) hl
    exact ⟨h.pc, h.accumulator⟩
  rw [show fuel.warp = 15 + 1 by decide, native_prepare_initial p neox ops input outside block warp 15 hb hw]
  exact first_stages_run p neox ops input block warp 0 4 11 _ hw (by decide) ready

#print axioms first_shuffle_code
#print axioms first_add_code
#print axioms xor_mask_bound
#print axioms first_stage_run
#print axioms first_stage_ready
#print axioms continue_shuffle
#print axioms bind_follow
#print axioms continue_fold
#print axioms first_stages_ready
#print axioms first_stages_run
#print axioms first_stages_preserves
#print axioms first_stages_input_reg
#print axioms native_first_four
end LarkNativeQKNormRope
