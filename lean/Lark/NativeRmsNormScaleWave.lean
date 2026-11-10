import Lark.NativeRmsNormLogicalFinish

/-! Complete actual scale wave: native entry, four logical-16 shuffle stages,
thread-zero scale store and the real second block cut, under declared warp fuel.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure LogicalReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row n : Nat) (s : State α) : Prop where
  mixed : MixedReady p row (41 + 3 * n) (logicalValues ops input row n) s
  tid : ∀ lane, lane < 16 → s.indices (cohortBase row 0 + lane) 1 = some (lane : Int)

theorem logical_ready_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row n : Nat)
    (s : State α) (ready : LogicalReady p ops input row n s) :
    LogicalReady p ops input row (n + 1)
      (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s) := by
  have hp := (cohort_step_preserves p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s).1
  refine ⟨mixed_step_ready p ops input row n s ready.mixed, ?_⟩
  intro lane hl
  exact (congrFun (congrFun hp (cohortBase row 0 + lane)) 1).trans (ready.tid lane hl)

def logicalTail (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : Nat → Nat → State α → State α
  | n, 0, s => logicalFinal p ops row (logicalValues ops input row n) s
  | n, remaining + 1, s => logicalTail p ops input row (n + 1) remaining
      (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s)

theorem continue_logical_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining extra : Nat) (s : State α) (hn : n + remaining = 3)
    (ready : LogicalReady p ops input row n s) :
    continueCohort p ops (cohortThreads row 0 64) (extra + remaining + 1) s =
      some (logicalTail p ops input row n remaining s) := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 3 := by omega
      subst n
      have hc := mixed_next p row 50 _ s ready.mixed .down 1 0 (.const (8 : Int)) (final_shuffle 3 (by decide))
      rewrite [continue_shuffle p ops _ _ _ s hc]
      exact logical_final_warp p ops row extra _ s ready.mixed ready.tid
  | succ remaining ih =>
      have hlt : n < 3 := by omega
      let next := cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s
      have hc := mixed_next p row (41 + 3 * n) _ s ready.mixed .down 1 0
        (.const (2 ^ n : Nat)) (final_shuffle n (by omega))
      have hf := mixed_stage_run p ops row n _ s hlt ready.mixed
      change continueCohort p ops (cohortThreads row 0 64) ((extra + remaining + 1) + 1) s = _
      rewrite [continue_fold p ops _ _ (extra + remaining + 1) s next hc hf]
      exact ih (n + 1) next (by omega) (logical_ready_step p ops input row n s ready)

theorem logical_entry_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    LogicalReady p ops input row 0 (midNative ops input row 0 s) := by
  refine ⟨mid_mixed_ready p ops input row s ready, ?_⟩
  intro lane hl
  have hi := (mid_native_preserves ops input row 0 s).2.1
  have hn : NativeIndices (cohortBase row 0 + lane) s := by
    simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using ready.indices lane (by omega)
  have hc := (logical_coords p row lane hl).1
  exact (congrFun (congrFun hi (cohortBase row 0 + lane)) 1).trans (by simpa only [hc] using hn.2.1)

def scaleWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  logicalTail p ops input row 0 3 (midNative ops input row 0 s)

/-- Actual physical-wave64 execution of the complete scale wave. -/
theorem scale_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row 0) fuel.warp s = some (scaleWave p ops input row s) := by
  rewrite [cohort_native_threads p row 0 (by decide), show fuel.warp = 7 + 1 by decide, runWarp_continue]
  exact sequence_ready
    (fun u => (cohortThreads row 0 64).foldlM
      (fun v t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane v) u)
    (continueCohort p ops (cohortThreads row 0 64) 7) (logicalTail p ops input row 0 3)
    s (midNative ops input row 0 s) (LogicalReady p ops input row 0)
    (mid_native_run p ops input row 0 s (by decide) ready) (logical_entry_ready p ops input row s ready)
    (fun u hu => continue_logical_tail p ops input row 0 3 3 u (by decide) hu)

theorem logical_tail_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α) (hn : n + remaining = 3) :
    (logicalTail p ops input row n remaining s).memory (scaleSlot row) = some (scale ops input row) := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 3 := by omega
      subst n
      have h := logical_final_value p ops row (logicalValues ops input row 3) s
      exact h.trans (congrArg some (show
        scaleFrom ops (ops.add (logicalValues ops input row 3 0) (logicalValues ops input row 3 8)) =
          scale ops input row from rfl))
  | succ remaining ih => exact ih (n + 1) _ (by omega)

theorem logical_tail_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α) :
    (logicalTail p ops input row n remaining s).indices = s.indices ∧
    (logicalTail p ops input row n remaining s).epochs = s.epochs := by
  induction remaining generalizing n s with
  | zero => exact logical_final_preserves p ops row _ s
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s)
      have h1 := cohort_step_preserves p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s
      exact ⟨h.1.trans h1.1, h.2.trans h1.2.2.1⟩

theorem logical_tail_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α) (hn : n + remaining = 3)
    (ready : LogicalReady p ops input row n s) :
    ∀ tid, tid < 64 → (logicalTail p ops input row n remaining s).pc (cohortBase row 0 + tid) = 55 := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 3 := by omega
      subst n
      intro tid ht
      by_cases ha : tid < 16
      · exact logical_final_active_pc p ops row tid _ s ha
      · exact (logical_final_other p ops row (cohortBase row 0 + tid) _ s (inactive_not_active row tid (by omega))).1.trans
          (ready.mixed.inactive tid (by omega) ht)
  | succ remaining ih => exact ih (n + 1) _ (by omega) (logical_ready_step p ops input row n s ready)

theorem logical_tail_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α)
    (he : ∀ lane, lane < 16 → (s.epochs (cohortBase row 0 + lane)).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (logicalTail p ops input row n remaining s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  induction remaining generalizing n s with
  | zero => exact logical_final_good p ops row _ s he good
  | succ remaining ih =>
      have hp := cohort_step_preserves p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s
      apply ih (n + 1)
      · intro lane hl
        exact (congrArg (fun epochs => (epochs (cohortBase row 0 + lane)).block) hp.2.2.1).trans (he lane hl)
      · intro access ha; exact good access (hp.2.2.2 ▸ ha)

theorem logical_tail_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining : Nat) (s : State α) (l : Location) (hl : l ≠ scaleSlot row) :
    (logicalTail p ops input row n remaining s).memory l = s.memory l := by
  induction remaining generalizing n s with
  | zero => exact logical_final_memory_other p ops row _ s l hl
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s)
      exact h.trans (congrFun (cohort_step_preserves p ops row 0 16 (41 + 3 * n) (2 ^ n) 16
        (logicalValues ops input row n) s).2.1 l)

theorem logical_tail_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row n remaining t : Nat) (s : State α) (ht : t ∉ cohortThreads row 0 16) :
    (logicalTail p ops input row n remaining s).pc t = s.pc t ∧
    (logicalTail p ops input row n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact logical_final_other p ops row t _ s ht
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (logicalValues ops input row n) s)
      have h1 := cohort_step_other p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 t (logicalValues ops input row n) s ht
      exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem scale_wave_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleWave p ops input row s).memory (scaleSlot row) = some (scale ops input row) :=
  logical_tail_value p ops input row 0 3 _ (by decide)

theorem scale_wave_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (scaleWave p ops input row s).indices = s.indices ∧ (scaleWave p ops input row s).epochs = s.epochs := by
  have h := logical_tail_preserves p ops input row 0 3 (midNative ops input row 0 s)
  have h1 := mid_native_preserves ops input row 0 s
  exact ⟨h.1.trans h1.2.1, h.2.trans h1.2.2⟩

theorem scale_wave_memory_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : l ≠ scaleSlot row) :
    (scaleWave p ops input row s).memory l = s.memory l :=
  (logical_tail_memory_other p ops input row 0 3 (midNative ops input row 0 s) l hl).trans
    (congrFun (mid_native_preserves ops input row 0 s).1 l)

theorem scale_wave_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t ∉ cohortThreads row 0 64) :
    (scaleWave p ops input row s).pc t = s.pc t ∧ (scaleWave p ops input row s).regs t = s.regs t := by
  have hn : t ∉ cohortThreads row 0 16 := by
    intro hm
    obtain ⟨lane, hl, he⟩ := (cohort_mem row 0 16 t).mp hm
    exact ht ((cohort_mem row 0 64 t).mpr ⟨lane, by omega, he⟩)
  have h := logical_tail_other p ops input row 0 3 t (midNative ops input row 0 s) hn
  have h1 := mid_fold_other row (fun u => u % 1024) (fun u => u % 1024 % 64)
    (fun u => warpSum ops input row (u % 1024 % 64)) (cohortThreads row 0 64) t s ht
  exact ⟨h.1.trans h1.1, h.2.trans h1.2⟩

theorem scale_wave_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α)
    (ready : MidReady p ops input row s) :
    ∀ tid, tid < 64 → (scaleWave p ops input row s).pc (cohortBase row 0 + tid) = 55 :=
  logical_tail_pc p ops input row 0 3 _ (by decide) (logical_entry_ready p ops input row s ready)

theorem scale_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α)
    (ready : MidReady p ops input row s) :
    ∀ access ∈ (scaleWave p ops input row s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  have hp := (mid_native_preserves ops input row 0 s).2.2
  apply logical_tail_good p ops input row 0 3 (midNative ops input row 0 s)
  · intro lane hl
    have h := (congrArg (fun epochs => (epochs (cohortBase row 0 + lane)).block) hp)
    exact h.trans (by simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using ready.epoch lane (by omega))
  · exact mid_native_good p ops input row 0 s (by decide) ready

#print axioms scale_wave_run
#print axioms logical_tail_value
#print axioms logical_tail_good
#print axioms scale_wave_value
#print axioms scale_wave_good
end LarkNativeRmsNorm
