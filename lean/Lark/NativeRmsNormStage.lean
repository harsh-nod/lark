import Lark.NativeRmsNormGuardFold
import Lark.NativeRmsNormPrefixFold

/-! Compose actual snapshot shuffle transport with the subsequent sequential
scalar lane fold. No shared-memory or full-launch theorem is asserted here.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def cohortStep (p : Shape) (ops : Ops α) (row warp width pc distance valid : Nat)
    (values : Nat → α) (s : State α) : State α :=
  let lanes := LarkPartitionCollective.nativeLane (geometry p)
  let a := fun t => values (lanes t)
  let b := fun t => values (downPeer width distance (lanes t))
  let shuffled := shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s
  guardedFold ops pc distance valid lanes a b (cohortThreads row warp width) shuffled

theorem cohort_step_run (p : Shape) (ops : Ops α) (row warp width pc distance valid : Nat)
    (bound : Index) (values : Nat → α) (s : State α)
    (hw : warp < 16) (hpos : 0 < width) (hwidth : width ≤ 64)
    (hs : [1, 2, 4, 8, 16, 32, 64].contains width = true) (hd : distance < width) (hd32 : distance ≤ 32)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc)
    (hi : ∀ lane, lane < width → s.indices (cohortBase row warp + lane) 2 = some (lane : Int))
    (hv : ∀ lane, lane < width → evalIndex (geometry p) (cohortBase row warp + lane) s bound = some (valid : Int))
    (hr : ∀ lane, lane < width → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (hshuffle : program[pc]? = some (.shuffle .down 1 0 (.const (distance : Int)) width))
    (hbranch : program[pc + 1]? = some (.scalar (.branch
      (.lt (.add (.ivar 2) (.const (distance : Int))) bound) (pc + 3))))
    (hadd : program[pc + 2]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (cut : LarkCollective.Cut) (hcut : ∀ (u : State α) t, u.pc t = pc + 3 → parked program u t = some cut) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp width) s).bind
      fun shuffled => (cohortThreads row warp width).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row warp width pc distance valid values s) := by
  rewrite [cohort_down_shuffle p row warp width distance pc s values hw hpos hwidth hs hd hp hr hshuffle]
  simp only [Option.some_bind]
  apply guarded_fold_run p ops pc distance valid bound
    (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp width) _ (cohort_nodup row warp width) hd32 (cut := cut)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    omega
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact hi lane hl
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    exact (index_of_indices (geometry p) _
      (shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s) s bound rfl).trans (hv lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    dsimp only
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (cohort_shuffled_fields p row warp width distance lane values s hw hwidth hl).2.1.trans (hr lane hl)
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    dsimp only
    rewrite [(cohort_coords p row warp lane hw (by omega)).2]
    exact (cohort_shuffled_fields p row warp width distance lane values s hw hwidth hl).2.2
  · intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    rewrite [(cohort_shuffled_fields p row warp width distance lane values s hw hwidth hl).1, hp lane hl]
    rfl
  · exact hbranch
  · exact hadd
  · exact hcut

theorem cohort_step_preserves (p : Shape) (ops : Ops α) (row warp width pc distance valid : Nat)
    (values : Nat → α) (s : State α) :
    (cohortStep p ops row warp width pc distance valid values s).indices = s.indices ∧
    (cohortStep p ops row warp width pc distance valid values s).memory = s.memory ∧
    (cohortStep p ops row warp width pc distance valid values s).epochs = s.epochs ∧
    (cohortStep p ops row warp width pc distance valid values s).trace = s.trace :=
  guarded_fold_preserves ops pc distance valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp width) _

theorem cohort_step_fields (p : Shape) (ops : Ops α) (row warp width pc distance valid lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hwidth : width ≤ 64) (hl : lane < width)
    (hr : s.regs (cohortBase row warp + lane) 0 = some (values lane)) :
    (cohortStep p ops row warp width pc distance valid values s).pc (cohortBase row warp + lane) = pc + 3 ∧
    (cohortStep p ops row warp width pc distance valid values s).regs (cohortBase row warp + lane) 0 =
      some (if lane + distance < valid then ops.add (values lane) (values (downPeer width distance lane)) else values lane) := by
  have hc := (cohort_coords p row warp lane hw (by omega)).2
  have hacc : (shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s).regs
      (cohortBase row warp + lane) 0 = some (values (LarkPartitionCollective.nativeLane (geometry p)
        (cohortBase row warp + lane))) := by
    rewrite [hc]
    exact (cohort_shuffled_fields p row warp width distance lane values s hw hwidth hl).2.1.trans hr
  have h := guarded_fold_member ops pc distance valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp width) _ (cohort_nodup row warp width) (cohortBase row warp + lane)
    ((cohort_mem row warp width _).mpr ⟨lane, hl, rfl⟩) hacc
  simpa only [hc] using h

theorem cohort_step_other (p : Shape) (ops : Ops α) (row warp width pc distance valid t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp width) :
    (cohortStep p ops row warp width pc distance valid values s).pc t = s.pc t ∧
    (cohortStep p ops row warp width pc distance valid values s).regs t = s.regs t := by
  have h := guarded_fold_other ops pc distance valid (LarkPartitionCollective.nativeLane (geometry p))
    (fun t => values (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t)))
    (cohortThreads row warp width) t (shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s) ht
  have hs := cohort_shuffled_other p row warp width distance t values s ht
  exact ⟨h.1.trans hs.1, h.2.trans hs.2⟩

/-- Execution's guarded update is the value recurrence, without reassociating addition. -/
theorem cohort_step_reduced (p : Shape) (ops : Ops α) (row warp width pc valid n lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hwidth : width ≤ 64) (hl : lane < width)
    (hr : s.regs (cohortBase row warp + lane) 0 = some (LarkDownReduction.reduced ops.add width valid values n lane)) :
    (cohortStep p ops row warp width pc (2 ^ n) valid
      (LarkDownReduction.reduced ops.add width valid values n) s).regs (cohortBase row warp + lane) 0 =
      some (LarkDownReduction.reduced ops.add width valid values (n + 1) lane) := by
  have h := (cohort_step_fields p ops row warp width pc (2 ^ n) valid lane
    (LarkDownReduction.reduced ops.add width valid values n) s hw hwidth hl hr).2
  exact h

structure StageReady (p : Shape) (row warp width pc valid : Nat) (bound : Index)
    (values : Nat → α) (s : State α) : Prop where
  pc : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc
  lane : ∀ lane, lane < width → s.indices (cohortBase row warp + lane) 2 = some (lane : Int)
  valid : ∀ lane, lane < width → evalIndex (geometry p) (cohortBase row warp + lane) s bound = some (valid : Int)
  acc : ∀ lane, lane < width → s.regs (cohortBase row warp + lane) 0 = some (values lane)

theorem cohort_step_ready (p : Shape) (ops : Ops α) (row warp width pc valid n : Nat)
    (bound : Index) (values : Nat → α) (s : State α) (hw : warp < 16) (hwidth : width ≤ 64)
    (ready : StageReady p row warp width pc valid bound (LarkDownReduction.reduced ops.add width valid values n) s) :
    StageReady p row warp width (pc + 3) valid bound
      (LarkDownReduction.reduced ops.add width valid values (n + 1))
      (cohortStep p ops row warp width pc (2 ^ n) valid
        (LarkDownReduction.reduced ops.add width valid values n) s) := by
  have hp := (cohort_step_preserves p ops row warp width pc (2 ^ n) valid
    (LarkDownReduction.reduced ops.add width valid values n) s).1
  constructor
  · intro lane hl
    exact (cohort_step_fields p ops row warp width pc (2 ^ n) valid lane
      (LarkDownReduction.reduced ops.add width valid values n) s hw hwidth hl (ready.acc lane hl)).1
  · intro lane hl
    exact (congrFun (congrFun hp (cohortBase row warp + lane)) 2).trans (ready.lane lane hl)
  · intro lane hl
    exact (index_of_indices (geometry p) _ _ s bound (congrFun hp _)).trans (ready.valid lane hl)
  · intro lane hl
    exact cohort_step_reduced p ops row warp width pc valid n lane values s hw hwidth hl (ready.acc lane hl)

theorem first_stage_run (p : Shape) (ops : Ops α) (row warp n : Nat) (values : Nat → α)
    (s : State α) (hw : warp < 16) (hn : n < 5)
    (ready : StageReady p row warp 64 (18 + 3 * n) (1024 - warp * 64) (.ivar 4) values s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64) s).bind
      fun shuffled => (cohortThreads row warp 64).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64) values s) := by
  have hd : 2 ^ n ≤ 32 := by
    have all : ∀ n : Fin 5, 2 ^ n.val ≤ 32 := by decide
    exact all ⟨n, hn⟩
  apply cohort_step_run p ops row warp 64 (18 + 3 * n) (2 ^ n) (1024 - warp * 64)
    (.ivar 4) values s hw (by decide) (by decide) (by decide) (by omega) hd
    ready.pc ready.lane ready.valid ready.acc (first_shuffle n (by omega))
    (first_guard_code n (by omega)).1 (first_guard_code n (by omega)).2 .shuffle
  intro u t ht
  unfold LarkCollective.parked
  rewrite [ht, show 18 + 3 * n + 3 = 18 + 3 * (n + 1) by omega, first_shuffle (n + 1) (by omega)]
  rfl

theorem final_stage_run (p : Shape) (ops : Ops α) (row n : Nat) (values : Nat → α)
    (s : State α) (hn : n < 3)
    (ready : StageReady p row 0 16 (41 + 3 * n) 16 (.const 16) values s) :
    ((LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row 0 16) s).bind
      fun shuffled => (cohortThreads row 0 16).foldlM
        (fun u t => runLane ops (layout p) (geometry p) program t fuel.lane u) shuffled) =
      some (cohortStep p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 values s) := by
  have hd : 2 ^ n < 16 := by
    have all : ∀ n : Fin 3, 2 ^ n.val < 16 := by decide
    exact all ⟨n, hn⟩
  apply cohort_step_run p ops row 0 16 (41 + 3 * n) (2 ^ n) 16 (.const 16) values s
    (by decide) (by decide) (by decide) (by decide) hd (by omega)
    ready.pc ready.lane ready.valid ready.acc (final_shuffle n (by omega))
    (final_guard_code n (by omega)).1 (final_guard_code n (by omega)).2 .shuffle
  intro u t ht
  unfold LarkCollective.parked
  rewrite [ht, show 41 + 3 * n + 3 = 41 + 3 * (n + 1) by omega, final_shuffle (n + 1) (by omega)]
  rfl

#print axioms cohort_step_run
#print axioms cohort_step_preserves
#print axioms cohort_step_reduced
#print axioms cohort_step_ready
#print axioms first_stage_run
#print axioms final_stage_run
end LarkNativeRmsNorm
