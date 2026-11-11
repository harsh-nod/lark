import Lark.NativeFusedRmsNormMidNative

/-! The mixed native wave: lower32 active at a shuffle and upper32 parked at
the real second block barrier. Cohort selection and physical fold order remain
those of the pinned scheduler; parked lane visits change no state or epochs.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inactiveThreads (row : Nat) : List Nat :=
  (List.range 32).map (fun i => cohortBase row 0 + (32 + i))

theorem physical_split (row : Nat) : cohortThreads row 0 64 = cohortThreads row 0 32 ++ inactiveThreads row := by
  have hr : List.range 64 = List.range 32 ++ (List.range 32).map (fun i => 32 + i) := by decide
  simpa only [cohortThreads, inactiveThreads, List.map_append, List.map_map, Function.comp_apply] using
    congrArg (List.map (fun i => cohortBase row 0 + i)) hr

theorem inactive_mem (row t : Nat) (ht : t ∈ inactiveThreads row) :
    ∃ tid, 32 ≤ tid ∧ tid < 64 ∧ t = cohortBase row 0 + tid := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  have hi := List.mem_range.mp hi
  exact ⟨32 + i, by omega, by omega, he.symm⟩

theorem mixed_filter (row : Nat) (pred : Nat → Bool)
    (ha : ∀ lane, lane < 32 → pred (cohortBase row 0 + lane) = true)
    (hb : ∀ tid, 32 ≤ tid → tid < 64 → pred (cohortBase row 0 + tid) = false) :
    (cohortThreads row 0 64).filter pred = cohortThreads row 0 32 := by
  have hactive : (cohortThreads row 0 32).filter pred = cohortThreads row 0 32 := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row 0 32 t).mp ht
    exact ha lane hl
  have hinactive : (inactiveThreads row).filter pred = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨tid, hl, hu, rfl⟩ := inactive_mem row t ht
    simp only [hb tid hl hu, Bool.false_eq_true, not_false_eq_true]
  rewrite [physical_split, List.filter_append, hactive, hinactive, List.append_nil]
  rfl

structure LogicalReady (row pc : Nat) (values : Nat → α) (s : State α) : Prop where
  pc : ∀ lane, lane < 32 → s.pc (cohortBase row 0 + lane) = pc
  accumulator : ∀ lane, lane < 32 → s.regs (cohortBase row 0 + lane) 0 = some (values lane)

structure MixedReady (row pc : Nat) (values : Nat → α) (s : State α) : Prop where
  active : LogicalReady row pc values s
  inactive : ∀ tid, 32 ≤ tid → tid < 64 → s.pc (cohortBase row 0 + tid) = 50

theorem mixed_next (row pc : Nat) (values : Nat → α) (s : State α) (ready : MixedReady row pc values s)
    (kind : LarkCollective.ShuffleKind) (dest src : Nat) (selector : Index)
    (code : program[pc]? = some (.shuffle kind dest src selector 32)) :
    LarkPartitionCollective.nextCohort program (cohortThreads row 0 64) s = some (cohortThreads row 0 32) := by
  have hne : pc ≠ 50 := by intro he; rewrite [he, second_barrier] at code; cases code
  have hf : (cohortThreads row 0 64).filter (LarkPartitionCollective.isShuffle program s) = cohortThreads row 0 32 := by
    apply mixed_filter row
    · intro lane hl; simp [LarkPartitionCollective.isShuffle, ready.active.pc lane hl, code]
    · intro tid hl hu; simp [LarkPartitionCollective.isShuffle, ready.inactive tid hl hu, second_barrier]
  have hp0 : s.pc (cohortBase row 0) = pc := by simpa only [Nat.add_zero] using ready.active.pc 0 (by decide)
  unfold LarkPartitionCollective.nextCohort
  rewrite [hf, cohort_head row 0 32 (by decide)]
  simp only [bind, pure, Option.bind]
  congr 1
  apply mixed_filter row
  · intro lane hl; simp [ready.active.pc lane hl, hp0]
  · intro tid hl hu; simp [ready.inactive tid hl hu, hp0, Ne.symm hne]

theorem lane_second_barrier (p : Shape) (ops : Ops α) (t : Nat) (s : State α) (hp : s.pc t = 50) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some s := by
  change LarkCollective.runLane ops (layout p) (geometry p) program t (511 + 1) s = _
  rewrite [LarkCollective.runLane]
  simp [LarkCollective.parked, hp, second_barrier]

theorem fold_second_barrier (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hp : ∀ t ∈ ts, s.pc t = 50) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) s = some s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rewrite [List.foldlM_cons, lane_second_barrier p ops t s (hp t (by simp))]
      simp only [bind, Option.some_bind]
      exact ih (by intro u hu; exact hp u (by simp [hu]))

theorem shuffle_physical_fold (p : Shape) (ops : Ops α) (row : Nat) (s next : State α)
    (ha : ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 32) s).bind
      fun shuffled => (cohortThreads row 0 32).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next)
    (hi : ∀ tid, 32 ≤ tid → tid < 64 → next.pc (cohortBase row 0 + tid) = 50) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 32) s).bind
      fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) = some next := by
  have hfun : (fun shuffled => (cohortThreads row 0 64).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      (fun shuffled => ((cohortThreads row 0 32).foldlM
        (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled).bind
        (fun after => (inactiveThreads row).foldlM
          (fun u t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane u) after)) := by
    funext shuffled
    rewrite [physical_split, List.foldlM_append]
    rfl
  rewrite [hfun, bind_follow _ _ _ next ha]
  apply fold_second_barrier p ops (inactiveThreads row) next
  intro t ht
  obtain ⟨tid, hl, hu, rfl⟩ := inactive_mem row t ht
  exact hi tid hl hu

theorem mid_mixed_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (_ready : MidReady p ops input row s) :
    MixedReady row 38 (blockPartial ops input row) (midNative ops input row 0 s) := by
  exact {
    active := {
      pc := by
        intro lane hl
        simpa only [Nat.zero_mul, Nat.zero_add, hl, ↓reduceIte] using mid_native_pc ops input row 0 lane s (by decide) (by omega)
      accumulator := fun lane hl => mid_native_acc ops input row lane s hl }
    inactive := fun tid hl hu => mid_native_inactive ops input row tid s hl hu }

#print axioms physical_split
#print axioms mixed_next
#print axioms fold_second_barrier
#print axioms shuffle_physical_fold
#print axioms mid_mixed_ready
end LarkNativeFusedRmsNorm
