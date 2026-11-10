import Lark.NativeRmsNormLogicalFold

/-! Final logical-16 source shuffle and scale store inside physical wave64.
The enclosing multiwave scale-phase and second resume are separate obligations.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def logicalFinal (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) : State α :=
  logicalLastFold ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) (shuffleUpdates 1 (cohortSnapshot p row 0 16 8 values) s)

theorem logical_coords (p : Shape) (row lane : Nat) (hl : lane < 16) :
    (cohortBase row 0 + lane) % 1024 = lane ∧
    LarkPartitionCollective.nativeLane (geometry p) (cohortBase row 0 + lane) = lane := by
  have hc := cohort_arithmetic row 0 lane (by decide) (by omega)
  exact ⟨by simpa only [Nat.zero_mul, Nat.zero_add] using hc.2.1,
    (cohort_coords p row 0 lane (by decide) (by omega)).2⟩

theorem logical_final_active_run (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α)
    (s : State α) (ready : StageReady p row 0 16 50 16 (.const 16) values s)
    (hi1 : ∀ lane, lane < 16 → s.indices (cohortBase row 0 + lane) 1 = some (lane : Int)) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 16).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (logicalFinal p ops row values s) := by
  rewrite [cohort_down_shuffle p row 0 16 8 50 s values (by decide) (by decide) (by decide) (by decide)
    (by decide) ready.pc ready.acc (final_shuffle 3 (by decide))]
  simp only [Option.some_bind]
  apply logical_fold_run p ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) _ (cohort_nodup row 0 16)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    exact (cohort_arithmetic row 0 lane (by decide) (by omega)).1
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(logical_coords p row lane hl).2]
    exact hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(logical_coords p row lane hl).1]
    exact hi1 lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(logical_coords p row lane hl).2]
    exact ready.lane lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(logical_coords p row lane hl).2]
    exact (cohort_shuffled_fields p row 0 16 8 lane values s (by decide) (by decide) hl).2.1.trans (ready.acc lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(logical_coords p row lane hl).2]
    exact (cohort_shuffled_fields p row 0 16 8 lane values s (by decide) (by decide) hl).2.2
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    rewrite [(cohort_shuffled_fields p row 0 16 8 lane values s (by decide) (by decide) hl).1, ready.pc lane hl]
    rfl

theorem logical_final_other (p : Shape) (ops : Ops α) (row t : Nat) (values : Nat → α) (s : State α)
    (ht : t ∉ cohortThreads row 0 16) :
    (logicalFinal p ops row values s).pc t = s.pc t ∧ (logicalFinal p ops row values s).regs t = s.regs t := by
  have h := logical_fold_other ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) t (shuffleUpdates 1 (cohortSnapshot p row 0 16 8 values) s) ht
  have hs := cohort_shuffled_other p row 0 16 8 t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

theorem logical_final_run (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α)
    (s : State α) (ready : MixedReady p row 50 values s)
    (hi1 : ∀ lane, lane < 16 → s.indices (cohortBase row 0 + lane) 1 = some (lane : Int)) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (logicalFinal p ops row values s) := by
  apply shuffle_physical_fold p ops row s _ (logical_final_active_run p ops row values s ready.active hi1)
  intro tid hl hu
  exact (logical_final_other p ops row (cohortBase row 0 + tid) values s (inactive_not_active row tid hl)).1.trans
    (ready.inactive tid hl hu)

theorem logical_final_preserves (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) :
    (logicalFinal p ops row values s).indices = s.indices ∧ (logicalFinal p ops row values s).epochs = s.epochs :=
  logical_fold_preserves ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) _

theorem logical_final_active_pc (p : Shape) (ops : Ops α) (row lane : Nat) (values : Nat → α)
    (s : State α) (hl : lane < 16) : (logicalFinal p ops row values s).pc (cohortBase row 0 + lane) = 55 :=
  logical_fold_pc ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) _ (cohort_nodup row 0 16) _ ((cohort_mem row 0 16 _).mpr ⟨lane, hl, rfl⟩)

theorem logical_final_good (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α)
    (he : ∀ lane, lane < 16 → (s.epochs (cohortBase row 0 + lane)).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (logicalFinal p ops row values s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  apply logical_fold_good p ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    exact (cohort_arithmetic row 0 lane (by decide) (by omega)).1
  · intro t ht; rfl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    exact he lane hl
  · exact good

theorem logical_cohort_cons (row : Nat) : cohortThreads row 0 16 = cohortBase row 0 ::
    (List.range 15).map (fun lane => cohortBase row 0 + (lane + 1)) := by
  have hr : List.range 16 = 0 :: (List.range 15).map (fun lane => lane + 1) := by decide
  simp only [cohortThreads, hr, List.map_cons, List.map_map, Nat.add_zero]
  rfl

theorem logical_cohort_memory (p : Shape) (ops : Ops α) (row : Nat) (a b : Nat → α) (s : State α) :
    (logicalLastFold ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p)) a b
      (cohortThreads row 0 16) s).memory =
      (logicalLastAfter ops (cohortBase row 0) row 0 0 (a (cohortBase row 0)) (b (cohortBase row 0)) s).memory := by
  let tail := (List.range 15).map (fun lane => cohortBase row 0 + (lane + 1))
  have hn : ∀ t ∈ tail, t % 1024 ≠ 0 := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := List.mem_map.mp ht
    have hl := List.mem_range.mp hl
    rewrite [(logical_coords p row (lane + 1) (by omega)).1]
    omega
  have hc := logical_coords p row 0 (by decide)
  have ht0 : cohortBase row 0 % 1024 = 0 := by simpa only [Nat.add_zero] using hc.1
  have hl0 : LarkPartitionCollective.nativeLane (geometry p) (cohortBase row 0) = 0 := by
    simpa only [Nat.add_zero] using hc.2
  unfold logicalLastFold
  rewrite [logical_cohort_cons, List.foldl_cons]
  dsimp only
  rewrite [ht0, hl0]
  exact logical_fold_memory_nonzero ops row (fun t => t % 1024)
    (LarkPartitionCollective.nativeLane (geometry p)) a b tail _ hn

theorem logical_final_value (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α) (s : State α) :
    (logicalFinal p ops row values s).memory (scaleSlot row) = some (scaleFrom ops (ops.add (values 0) (values 8))) := by
  have hm := logical_cohort_memory p ops row
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (shuffleUpdates 1 (cohortSnapshot p row 0 16 8 values) s)
  have h := (congrFun hm (scaleSlot row)).trans (logical_last_value ops (cohortBase row 0) row _ _ _)
  have hc : LarkPartitionCollective.nativeLane (geometry p) (cohortBase row 0) = 0 := by
    simpa only [Nat.add_zero] using (logical_coords p row 0 (by decide)).2
  simpa only [hc, downPeer, Nat.zero_add, show 8 < 16 by decide, ↓reduceIte] using h

theorem logical_final_memory_other (p : Shape) (ops : Ops α) (row : Nat) (values : Nat → α)
    (s : State α) (l : Location) (hl : l ≠ scaleSlot row) :
    (logicalFinal p ops row values s).memory l = s.memory l :=
  logical_fold_memory_other ops row (fun t => t % 1024) (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer 16 8 (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row 0 16) _ l hl

theorem cohort_second_barrier (row warp width : Nat) (s : State α) (hpos : 0 < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = 55) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp width) s = none ∧
    LarkCollective.converged program (cohortThreads row warp width) s = some .block := by
  have hp0 : s.pc (cohortBase row warp) = 55 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp width).filter (LarkPartitionCollective.isShuffle program s) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [LarkPartitionCollective.isShuffle, hp lane hl, second_barrier]
  have ha : (cohortThreads row warp width).all (fun t => s.pc t == s.pc (cohortBase row warp)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [hp lane hl, hp0]
  constructor
  · simp [LarkPartitionCollective.nextCohort, hf]
  · unfold LarkCollective.converged
    rewrite [cohort_head row warp width hpos]
    simp only [bind, pure, Option.bind, ha, ↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0, second_barrier]
    rfl

theorem warp_at_second_barrier (p : Shape) (ops : Ops α) (row warp width extra : Nat)
    (s next : State α) (hpos : 0 < width)
    (hf : (cohortThreads row warp width).foldlM
      (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) s = some next)
    (hp : ∀ lane, lane < width → next.pc (cohortBase row warp + lane) = 55) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (cohortThreads row warp width) (extra + 1) s = some next := by
  rcases cohort_second_barrier row warp width next hpos hp with ⟨hc, hconverged⟩
  rewrite [LarkPartitionCollective.runWarp, hf]
  simp only [bind, pure, Option.some_bind, hc, hconverged, reduceCtorEq, ↓reduceIte]

theorem logical_final_warp (p : Shape) (ops : Ops α) (row extra : Nat) (values : Nat → α)
    (s : State α) (ready : MixedReady p row 50 values s)
    (hi1 : ∀ lane, lane < 16 → s.indices (cohortBase row 0 + lane) 1 = some (lane : Int)) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (cohortThreads row 0 64) (extra + 1) shuffled) = some (logicalFinal p ops row values s) := by
  have hs := cohort_down_shuffle p row 0 16 8 50 s values (by decide) (by decide) (by decide) (by decide)
    (by decide) ready.active.pc ready.active.acc (final_shuffle 3 (by decide))
  have hf := logical_final_run p ops row values s ready hi1
  rewrite [hs, Option.some_bind] at hf
  rewrite [hs, Option.some_bind]
  apply warp_at_second_barrier p ops row 0 64 extra _ (logicalFinal p ops row values s) (by decide) hf
  intro tid ht
  by_cases ha : tid < 16
  · exact logical_final_active_pc p ops row tid values s ha
  · exact (logical_final_other p ops row (cohortBase row 0 + tid) values s
      (inactive_not_active row tid (by omega))).1.trans (ready.inactive tid (by omega) ht)

#print axioms logical_final_run
#print axioms logical_final_active_pc
#print axioms logical_final_good
#print axioms logical_final_value
#print axioms logical_final_warp
end LarkNativeRmsNorm
