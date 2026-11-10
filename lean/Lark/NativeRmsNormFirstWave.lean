import Lark.NativeRmsNormSchedule

/-! Compose the actual prefix and six native shuffle stages through the first
block barrier. This module concerns one physical wave, not the whole block.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def waveValues (ops : Ops α) (input : Nat → Nat → α) (row warp n : Nat) : Nat → α :=
  LarkDownReduction.reduced ops.add 64 (1024 - warp * 64)
    (fun lane => threadSum ops input row (warp * 64 + lane)) n

structure FirstReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) : Prop where
  stage : StageReady p row warp 64 (18 + 3 * n) (1024 - warp * 64) (.ivar 4)
    (waveValues ops input row warp n) s
  warpIndex : ∀ lane, lane < 64 → s.indices (cohortBase row warp + lane) 3 = some (warp : Int)

theorem ready_pc_eq (p : Shape) (row warp width pc next valid : Nat) (bound : Index)
    (values : Nat → α) (s : State α) (he : pc = next)
    (ready : StageReady p row warp width pc valid bound values s) :
    StageReady p row warp width next valid bound values s := by
  subst next
  exact ready

theorem first_ready_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hw : warp < 16) (ready : FirstReady p ops input row warp n s) :
    FirstReady p ops input row warp (n + 1)
      (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64)
        (waveValues ops input row warp n) s) := by
  have hr := cohort_step_ready p ops row warp 64 (18 + 3 * n) (1024 - warp * 64) n (.ivar 4)
    (fun lane => threadSum ops input row (warp * 64 + lane)) s hw (by decide) ready.stage
  have hp := (cohort_step_preserves p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64)
    (waveValues ops input row warp n) s).1
  constructor
  · exact ready_pc_eq p row warp 64 (18 + 3 * n + 3) (18 + 3 * (n + 1))
      (1024 - warp * 64) (.ivar 4) _ _ (by omega) hr
  · intro lane hl
    exact (congrFun (congrFun hp (cohortBase row warp + lane)) 3).trans (ready.warpIndex lane hl)

def waveTail (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) :
    Nat → Nat → State α → State α
  | n, 0, s => lastWave p ops row warp (1024 - warp * 64) (waveValues ops input row warp n) s
  | n, remaining + 1, s => waveTail p ops input row warp (n + 1) remaining
      (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64)
        (waveValues ops input row warp n) s)

theorem continue_wave_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining extra : Nat) (s : State α) (hn : n + remaining = 5)
    (hw : warp < 16) (ready : FirstReady p ops input row warp n s) :
    continueCohort p ops (cohortThreads row warp 64) (extra + remaining + 1) s =
      some (waveTail p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 5 := by omega
      subst n
      have hc := cohort_next row warp 64 33 s (by decide) ready.stage.pc
        .down 1 0 (.const (32 : Int)) (first_shuffle 5 (by decide))
      rewrite [continue_shuffle p ops _ _ _ s hc]
      exact last_wave_warp p ops row warp (1024 - warp * 64) extra
        (waveValues ops input row warp 5) s hw ready.stage ready.warpIndex
  | succ remaining ih =>
      have hlt : n < 5 := by omega
      let next := cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64)
        (waveValues ops input row warp n) s
      have hc := cohort_next row warp 64 (18 + 3 * n) s (by decide) ready.stage.pc
        .down 1 0 (.const (2 ^ n : Nat)) (first_shuffle n (by omega))
      have hf := first_stage_run p ops row warp n (waveValues ops input row warp n) s hw hlt ready.stage
      change continueCohort p ops (cohortThreads row warp 64) ((extra + remaining + 1) + 1) s = _
      rewrite [continue_fold p ops _ _ (extra + remaining + 1) s next hc hf]
      exact ih (n + 1) next (by omega) (first_ready_step p ops input row warp n s hw ready)

theorem first_ready_of_prefix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (hready : ∀ lane, lane < 64 → PrefixReady ops input (cohortBase row warp + lane) s) :
    FirstReady p ops input row warp 0 s := by
  constructor
  · exact cohort_ready_of_prefix p ops input row warp s hw hready
  · intro lane hl
    have h := (hready lane hl).2.2.2.2.2.1
    rewrite [(cohort_arithmetic row warp lane hw hl).2.2.2] at h
    exact h

def firstWave (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  waveTail p ops input row warp 0 5 (prefixFold ops input (cohortThreads row warp 64) s)

/-- Complete actual native wave execution under the declared eight-iteration
warp fuel, for every input and any cohort-entry state with readable inputs. -/
theorem first_wave_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16) (reads : Reads p input s)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 0) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) fuel.warp s = some (firstWave p ops input row warp s) := by
  have hbound : ∀ t ∈ cohortThreads row warp 64, t < p.rows * 1024 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    unfold cohortBase
    omega
  have hpc : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact hp lane hl
  have hready : FirstReady p ops input row warp 0 (prefixFold ops input (cohortThreads row warp 64) s) :=
    first_ready_of_prefix p ops input row warp _ hw (by
      intro lane hl
      exact prefix_fold_member ops input _ s (cohort_nodup row warp 64) _
        ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩))
  rewrite [cohort_native_threads p row warp hw, show fuel.warp = 7 + 1 by decide, runWarp_continue]
  exact sequence_ready
    (fun u => (cohortThreads row warp 64).foldlM
      (fun v t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane v) u)
    (continueCohort p ops (cohortThreads row warp 64) 7)
    (waveTail p ops input row warp 0 5) s (prefixFold ops input (cohortThreads row warp 64) s)
    (FirstReady p ops input row warp 0)
    (prefix_fold_run p ops input _ s (cohort_nodup row warp 64) reads hbound hpc) hready
    (fun u hu => continue_wave_tail p ops input row warp 0 5 1 u (by decide) hw hu)

theorem wave_tail_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) :
    (waveTail p ops input row warp n remaining s).indices = s.indices ∧
    (waveTail p ops input row warp n remaining s).epochs = s.epochs := by
  induction remaining generalizing n s with
  | zero => exact last_wave_preserves p ops row warp _ _ s
  | succ remaining ih =>
      have h := ih (n + 1) (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s)
      have h1 := cohort_step_preserves p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s
      exact ⟨h.1.trans h1.1, h.2.trans h1.2.2.1⟩

theorem wave_tail_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (waveTail p ops input row warp n remaining s) := by
  induction remaining generalizing n s with
  | zero => exact last_wave_reads p ops input row warp _ _ s reads
  | succ remaining ih =>
      exact ih (n + 1) _ (reads_of_memory p input s _ reads
        (cohort_step_preserves p ops row warp 64 (18 + 3 * n) (2 ^ n)
          (1024 - warp * 64) (waveValues ops input row warp n) s).2.1)

theorem wave_tail_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hw : warp < 16)
    (he : ∀ lane, lane < 64 → (s.epochs (cohortBase row warp + lane)).block = 0)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (waveTail p ops input row warp n remaining s).trace,
      LarkReductionFootprint.Good (traversal p) 0 access := by
  induction remaining generalizing n s with
  | zero => exact last_wave_good p ops row warp _ _ s hw he good
  | succ remaining ih =>
      have hp := cohort_step_preserves p ops row warp 64 (18 + 3 * n) (2 ^ n)
        (1024 - warp * 64) (waveValues ops input row warp n) s
      apply ih (n + 1)
      · intro lane hl
        exact (congrArg (fun epochs => (epochs (cohortBase row warp + lane)).block) hp.2.2.1).trans (he lane hl)
      · intro access ha
        exact good access (hp.2.2.2 ▸ ha)

theorem wave_tail_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hn : n + remaining = 5) (hw : warp < 16) :
    (waveTail p ops input row warp n remaining s).memory (partialCell (cohortBase row warp) warp) =
      some (warpSum ops input row warp) := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 5 := by omega
      subst n
      have h := last_wave_partial p ops row warp (1024 - warp * 64) (waveValues ops input row warp 5) s hw
      exact h.trans (congrArg some (show
        (if 32 < 1024 - warp * 64 then
          ops.add (waveValues ops input row warp 5 0) (waveValues ops input row warp 5 32)
        else waveValues ops input row warp 5 0) = warpSum ops input row warp from rfl))
  | succ remaining ih => exact ih (n + 1) _ (by omega)

theorem wave_tail_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n remaining : Nat) (s : State α) (hn : n + remaining = 5) (hw : warp < 16)
    (ready : FirstReady p ops input row warp n s) :
    ∀ lane, lane < 64 → (waveTail p ops input row warp n remaining s).pc (cohortBase row warp + lane) = 38 := by
  induction remaining generalizing n s with
  | zero =>
      have he : n = 5 := by omega
      subst n
      intro lane hl
      exact (last_wave_fields p ops row warp _ lane _ s hw hl (ready.stage.acc lane hl)).1
  | succ remaining ih =>
      exact ih (n + 1) _ (by omega) (first_ready_step p ops input row warp n s hw ready)

theorem first_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    FirstReady p ops input row warp 0 (prefixFold ops input (cohortThreads row warp 64) s) :=
  first_ready_of_prefix p ops input row warp _ hw (by
    intro lane hl
    exact prefix_fold_member ops input _ s (cohort_nodup row warp 64) _
      ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩))

/-- Actual completion and the intended partial value, with input preservation,
unchanged epochs and classification of every actual access, for any input and
initial outside memory. This is one physical wave, not the full launch. -/
theorem first_wave_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    ∃ final,
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row warp) fuel.warp (initial (layout p) input outside) = some final ∧
      (∀ lane, lane < 64 → final.pc (cohortBase row warp + lane) = 38) ∧
      final.memory (partialCell (cohortBase row warp) warp) = some (warpSum ops input row warp) ∧
      Reads p input final ∧ final.epochs = (initial (layout p) input outside).epochs ∧
      (∀ access ∈ final.trace, LarkReductionFootprint.Good (traversal p) 0 access) := by
  let start := initial (layout p) input outside
  let prefixed := prefixFold ops input (cohortThreads row warp 64) start
  have hpres := prefix_fold_preserves ops input (cohortThreads row warp 64) start
  have hread := reads_of_memory p input start prefixed (initial_reads p input outside) hpres.1
  refine ⟨firstWave p ops input row warp start,
    first_wave_run p ops input row warp start hr hw (initial_reads p input outside) (by intro lane hl; rfl),
    wave_tail_pc p ops input row warp 0 5 prefixed (by decide) hw (first_prefix_ready p ops input row warp start hw),
    wave_tail_partial p ops input row warp 0 5 prefixed (by decide) hw,
    wave_tail_reads p ops input row warp 0 5 prefixed hread,
    (wave_tail_preserves p ops input row warp 0 5 prefixed).2.trans hpres.2, ?_⟩
  apply wave_tail_good p ops input row warp 0 5 prefixed hw
  · intro lane hl
    exact (congrArg (fun epochs => (epochs (cohortBase row warp + lane)).block) hpres.2).trans rfl
  · exact prefix_fold_good p ops input _ start (by intro access ha; cases ha)

#print axioms first_ready_step
#print axioms continue_wave_tail
#print axioms first_wave_run
#print axioms wave_tail_partial
#print axioms wave_tail_good
#print axioms first_wave_from_initial
end LarkNativeRmsNorm
