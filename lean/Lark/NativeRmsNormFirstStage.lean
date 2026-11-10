import Lark.NativeRmsNormStage

/-! Bind the first actual wave stage to the source prefix for arbitrary inputs.
Later stages, stores, barriers and the full launch remain separate obligations.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem cohort_arithmetic (row warp lane : Nat) (hw : warp < 16) (hl : lane < 64) :
    (cohortBase row warp + lane) / 1024 = row ∧
    (cohortBase row warp + lane) % 1024 = warp * 64 + lane ∧
    ((cohortBase row warp + lane) % 1024) % 64 = lane ∧
    ((cohortBase row warp + lane) % 1024) / 64 = warp := by
  have hm : (cohortBase row warp + lane) % 1024 = warp * 64 + lane := by
    unfold cohortBase
    omega
  have hd : (cohortBase row warp + lane) / 1024 = row := by
    unfold cohortBase
    omega
  refine ⟨hd, hm, ?_, ?_⟩
  · rewrite [hm]
    omega
  · rewrite [hm]
    omega

theorem cohort_ready_of_prefix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16)
    (hready : ∀ lane, lane < 64 → PrefixReady ops input (cohortBase row warp + lane) s) :
    StageReady p row warp 64 18 (1024 - warp * 64) (.ivar 4)
      (fun lane => threadSum ops input row (warp * 64 + lane)) s := by
  constructor
  · intro lane hl; exact (hready lane hl).1
  · intro lane hl
    have h := (hready lane hl).2.2.2.2.1
    rewrite [(cohort_arithmetic row warp lane hw hl).2.2.1] at h
    exact h
  · intro lane hl
    have h := (hready lane hl).2.2.2.2.2.2
    rewrite [(cohort_arithmetic row warp lane hw hl).2.2.2] at h
    change s.indices
      (cohortBase row warp + lane) 4 = some ((1024 - warp * 64 : Nat) : Int)
    exact h.trans (congrArg some (by omega))
  · intro lane hl
    have h := (hready lane hl).2.1
    rcases cohort_arithmetic row warp lane hw hl with ⟨hr, ht, hla, hwa⟩
    simpa only [hr, ht] using h

theorem prefix_cohort_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) :
    StageReady p row warp 64 18 (1024 - warp * 64) (.ivar 4)
      (fun lane => threadSum ops input row (warp * 64 + lane))
      (prefixFold ops input (cohortThreads row warp 64) s) :=
  cohort_ready_of_prefix p ops input row warp _ hw (by
    intro lane hl
    exact prefix_fold_member ops input _ s (cohort_nodup row warp 64) _
      ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩))

theorem first_stage_zero_run (p : Shape) (ops : Ops α) (row warp : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16)
    (ready : StageReady p row warp 64 18 (1024 - warp * 64) (.ivar 4) values s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) s).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row warp 64 18 1 (1024 - warp * 64) values s) := by
  apply cohort_step_run p ops row warp 64 18 1 (1024 - warp * 64) (.ivar 4) values s
    hw (by decide) (by decide) (by decide) (by decide) (by decide)
    ready.pc ready.lane ready.valid ready.acc (first_shuffle 0 (by decide))
    (first_guard_code 0 (by decide)).1 (first_guard_code 0 (by decide)).2 .shuffle
  intro u t ht
  unfold LarkCollective.parked
  rewrite [ht]
  change (match program[18 + 3 * 1]? with
    | some (.scalar (.barrier c)) => some (LarkCollective.scalarCut c)
    | some (.scalar .halt) => some .halt
    | some (.shuffle ..) => some .shuffle
    | _ => none) = _
  rewrite [first_shuffle 1 (by decide)]
  rfl

theorem sequence_ready (f g : State α → Option (State α)) (G : State α → State α)
    (s next : State α) (P : State α → Prop) (hf : f s = some next) (hp : P next)
    (hg : ∀ u, P u → g u = some (G u)) : (f s).bind g = some (G next) := by
  rewrite [hf]
  exact hg next hp

/-- Actual scheduler prefix fold, first snapshot shuffle and first guarded fold,
for every input and any state with the source cohort at entry. -/
theorem first_stage_from_prefix (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16) (reads : Reads p input s)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 0) :
    ((cohortThreads row warp 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s).bind
      (fun prefixed => (LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) prefixed).bind
        fun shuffled => (cohortThreads row warp 64).foldlM
          (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row warp 64 18 1 (1024 - warp * 64)
        (fun lane => threadSum ops input row (warp * 64 + lane))
        (prefixFold ops input (cohortThreads row warp 64) s)) := by
  have hbound : ∀ t ∈ cohortThreads row warp 64, t < p.rows * 1024 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    unfold cohortBase
    omega
  have hpc : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp 64 t).mp ht
    exact hp lane hl
  exact sequence_ready
    (fun u => (cohortThreads row warp 64).foldlM
      (fun v t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane v) u)
    (fun u => (LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) u).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun v t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane v) shuffled)
    (fun u => cohortStep p ops row warp 64 18 1 (1024 - warp * 64)
      (fun lane => threadSum ops input row (warp * 64 + lane)) u)
    s (prefixFold ops input (cohortThreads row warp 64) s)
    (StageReady p row warp 64 18 (1024 - warp * 64) (.ivar 4)
      (fun lane => threadSum ops input row (warp * 64 + lane)))
    (prefix_fold_run p ops input (cohortThreads row warp 64) s
      (cohort_nodup row warp 64) reads hbound hpc)
    (prefix_cohort_ready p ops input row warp s hw)
    (fun u hu => first_stage_zero_run p ops row warp _ u hw hu)

#print axioms prefix_cohort_ready
#print axioms first_stage_from_prefix
end LarkNativeRmsNorm
