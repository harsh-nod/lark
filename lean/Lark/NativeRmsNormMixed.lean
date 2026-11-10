import Lark.NativeRmsNormMidNative

/-! Mixed physical wave: sixteen active logical lanes and forty-eight lanes at
the second block barrier. Selection and lane-fold order match the real scheduler.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def inactiveThreads (row : Nat) : List Nat :=
  (List.range 48).map (fun i => cohortBase row 0 + (16 + i))

theorem physical_split (row : Nat) :
    cohortThreads row 0 64 = cohortThreads row 0 16 ++ inactiveThreads row := by
  have hr : List.range 64 = List.range 16 ++ (List.range 48).map (fun i => 16 + i) := by decide
  simpa only [cohortThreads, inactiveThreads, List.map_append, List.map_map, Function.comp_apply] using
    congrArg (List.map (fun i => cohortBase row 0 + i)) hr

theorem inactive_mem (row t : Nat) (ht : t ∈ inactiveThreads row) :
    ∃ tid, 16 ≤ tid ∧ tid < 64 ∧ t = cohortBase row 0 + tid := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  have hi := List.mem_range.mp hi
  exact ⟨16 + i, by omega, by omega, he.symm⟩

theorem mixed_filter (row : Nat) (pred : Nat → Bool)
    (ha : ∀ lane, lane < 16 → pred (cohortBase row 0 + lane) = true)
    (hb : ∀ tid, 16 ≤ tid → tid < 64 → pred (cohortBase row 0 + tid) = false) :
    (cohortThreads row 0 64).filter pred = cohortThreads row 0 16 := by
  have hactive : (cohortThreads row 0 16).filter pred = cohortThreads row 0 16 := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 16 t).mp ht
    exact ha lane hl
  have hinactive : (inactiveThreads row).filter pred = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨tid, hl, hu, rfl⟩ := inactive_mem row t ht
    simp only [hb tid hl hu, Bool.false_eq_true, not_false_eq_true]
  rewrite [physical_split, List.filter_append, hactive, hinactive, List.append_nil]
  rfl

structure MixedReady (p : Shape) (row pc : Nat) (values : Nat → α) (s : State α) : Prop where
  active : StageReady p row 0 16 pc 16 (.const 16) values s
  inactive : ∀ tid, 16 ≤ tid → tid < 64 → s.pc (cohortBase row 0 + tid) = 55

theorem mixed_next (p : Shape) (row pc : Nat) (values : Nat → α) (s : State α)
    (ready : MixedReady p row pc values s) (kind : LarkCollective.ShuffleKind) (dest src : Nat) (selector : Index)
    (code : program[pc]? = some (.shuffle kind dest src selector 16)) :
    LarkPartitionCollective.nextCohort program (cohortThreads row 0 64) s = some (cohortThreads row 0 16) := by
  have hne : pc ≠ 55 := by
    intro he
    rewrite [he, second_barrier] at code
    cases code
  have hfilter : (cohortThreads row 0 64).filter (LarkPartitionCollective.isShuffle program s) =
      cohortThreads row 0 16 := by
    apply mixed_filter row
    · intro lane hl
      simp [LarkPartitionCollective.isShuffle, ready.active.pc lane hl, code]
    · intro tid hl hu
      simp [LarkPartitionCollective.isShuffle, ready.inactive tid hl hu, second_barrier]
  have hp0 : s.pc (cohortBase row 0) = pc := by
    simpa only [Nat.add_zero] using ready.active.pc 0 (by decide)
  unfold LarkPartitionCollective.nextCohort
  rewrite [hfilter, cohort_head row 0 16 (by decide)]
  simp only [bind, pure, Option.bind]
  congr 1
  apply mixed_filter row
  · intro lane hl
    simp [ready.active.pc lane hl, hp0]
  · intro tid hl hu
    simp [ready.inactive tid hl hu, hp0, Ne.symm hne]

theorem lane_second_barrier (p : Shape) (ops : Ops α) (t : Nat) (s : State α) (hp : s.pc t = 55) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some s := by
  change LarkCollective.runLane ops (layout p) (geometry p) program t (255 + 1) s = _
  rewrite [LarkCollective.runLane]
  simp [LarkCollective.parked, hp, second_barrier]

theorem fold_second_barrier (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hp : ∀ t ∈ ts, s.pc t = 55) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s = some s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rewrite [List.foldlM_cons, lane_second_barrier p ops t s (hp t (by simp))]
      simp only [bind, Option.some_bind]
      exact ih (by intro u hu; exact hp u (by simp [hu]))

/-- Complete the physical lane fold by visiting the parked inactive suffix in
its original source order. Those lane calls produce no state or epoch update. -/
theorem shuffle_physical_fold (p : Shape) (ops : Ops α) (row : Nat) (s next : State α)
    (ha : ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 16).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next)
    (hi : ∀ tid, 16 ≤ tid → tid < 64 → next.pc (cohortBase row 0 + tid) = 55) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next := by
  have hfun : (fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      (fun shuffled => ((cohortThreads row 0 16).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled).bind
        (fun after => (inactiveThreads row).foldlM
          (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) after)) := by
    funext shuffled
    rewrite [physical_split, List.foldlM_append]
    rfl
  rewrite [hfun]
  rewrite [bind_follow _ _ _ next ha]
  apply fold_second_barrier p ops (inactiveThreads row) next
  intro t ht
  obtain ⟨tid, hl, hu, rfl⟩ := inactive_mem row t ht
  exact hi tid hl hu

theorem mid_mixed_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : MidReady p ops input row s) :
    MixedReady p row 41 (warpSum ops input row) (midNative ops input row 0 s) :=
  ⟨mid_native_ready p ops input row s ready, fun tid hl hu => mid_native_inactive ops input row tid s hl hu⟩

#print axioms mixed_next
#print axioms shuffle_physical_fold
#print axioms mid_mixed_ready
end LarkNativeRmsNorm
