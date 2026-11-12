import Lark.NativeSglangRmsNormAdd

/-! An actual native scheduler iteration after a shuffle snapshot: each lane
adds its two registers, parks at the following shuffle, and joins the next
logical32 snapshot. Neither operation changes memory, indices, epochs or trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] addFold

def cohortAdd (p : Shape) (ops : Ops α) (row warp active pc : Nat)
    (a b : Nat → α) (s : State α) : State α :=
  addFold ops pc
    (fun t => a (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => b (LarkPartitionCollective.nativeLane (geometry p) t))
    (cohortThreads row warp active) s

theorem cohort_add_fields (p : Shape) (ops : Ops α) (row warp active pc lane : Nat)
    (a b : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    (cohortAdd p ops row warp active pc a b s).pc (cohortBase row warp + lane) = pc + 1 ∧
    (cohortAdd p ops row warp active pc a b s).regs (cohortBase row warp + lane) 0 =
      some (ops.add (a lane) (b lane)) := by
  have h := add_fold_member ops pc
    (fun t => a (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => b (LarkPartitionCollective.nativeLane (geometry p) t))
    (cohortThreads row warp active) s (cohort_nodup row warp active) _
    ((cohort_mem row warp active _).mpr ⟨lane,hl,rfl⟩)
  simpa only [cohortAdd,(cohort_coords p row warp lane hw (by omega)).2] using h

theorem cohort_add_preserves (p : Shape) (ops : Ops α) (row warp active pc : Nat)
    (a b : Nat → α) (s : State α) :
    (cohortAdd p ops row warp active pc a b s).memory = s.memory ∧
    (cohortAdd p ops row warp active pc a b s).indices = s.indices ∧
    (cohortAdd p ops row warp active pc a b s).epochs = s.epochs ∧
    (cohortAdd p ops row warp active pc a b s).trace = s.trace :=
  add_fold_preserves ops pc _ _ _ s

theorem cohort_add_other (p : Shape) (ops : Ops α) (row warp active pc t : Nat)
    (a b : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    (cohortAdd p ops row warp active pc a b s).pc t = s.pc t ∧
    (cohortAdd p ops row warp active pc a b s).regs t = s.regs t :=
  add_fold_other ops pc _ _ _ t s ht

theorem cohort_add_run (p : Shape) (repaired : Bool) (ops : Ops α)
    (row warp active pc mask : Nat) (a b : Nat → α) (s : State α)
    (hw : warp < 16) (ha : active ≤ 64)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (h0 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (a lane))
    (h1 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 1 = some (b lane))
    (code : (program repaired)[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (nextCode : (program repaired)[pc+1]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    (cohortThreads row warp active).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s =
      some (cohortAdd p ops row warp active pc a b s) := by
  apply add_fold_run p repaired ops pc _ _ _ s (cohort_nodup row warp active) (cut := .shuffle)
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    exact hp lane hl
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    simpa only [(cohort_coords p row warp lane hw (by omega)).2] using h0 lane hl
  · intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    simpa only [(cohort_coords p row warp lane hw (by omega)).2] using h1 lane hl
  · exact code
  · intro u t _ hpc
    simp only [LarkCollective.parked,hpc,nextCode]

def followingSnapshot (p : Shape) (ops : Ops α) (row warp active pc mask : Nat)
    (a b : Nat → α) (s : State α) : State α :=
  shuffleUpdates 1 (xorSnapshot p row warp active mask (fun lane => ops.add (a lane) (b lane)))
    (cohortAdd p ops row warp active pc a b s)

theorem following_snapshot_fields (p : Shape) (ops : Ops α) (row warp active pc mask lane : Nat)
    (a b : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    (followingSnapshot p ops row warp active pc mask a b s).pc (cohortBase row warp + lane) = pc + 2 ∧
    (followingSnapshot p ops row warp active pc mask a b s).regs (cohortBase row warp + lane) 0 =
      some (ops.add (a lane) (b lane)) ∧
    (followingSnapshot p ops row warp active pc mask a b s).regs (cohortBase row warp + lane) 1 =
      some (ops.add (a (xorPeer32 lane mask)) (b (xorPeer32 lane mask))) := by
  have add := cohort_add_fields p ops row warp active pc lane a b s hw ha hl
  have shuffled := xor_shuffled_fields p row warp active mask lane
    (fun lane => ops.add (a lane) (b lane)) (cohortAdd p ops row warp active pc a b s) hw ha hl
  exact ⟨by simpa only [add.1,Nat.add_assoc] using shuffled.1,
    shuffled.2.1.trans add.2,shuffled.2.2⟩

theorem following_snapshot_preserves (p : Shape) (ops : Ops α) (row warp active pc mask : Nat)
    (a b : Nat → α) (s : State α) :
    (followingSnapshot p ops row warp active pc mask a b s).memory = s.memory ∧
    (followingSnapshot p ops row warp active pc mask a b s).indices = s.indices ∧
    (followingSnapshot p ops row warp active pc mask a b s).epochs = s.epochs ∧
    (followingSnapshot p ops row warp active pc mask a b s).trace = s.trace :=
  cohort_add_preserves p ops row warp active pc a b s

theorem following_snapshot_other (p : Shape) (ops : Ops α) (row warp active pc mask t : Nat)
    (a b : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    (followingSnapshot p ops row warp active pc mask a b s).pc t = s.pc t ∧
    (followingSnapshot p ops row warp active pc mask a b s).regs t = s.regs t := by
  have h := xor_shuffled_other p row warp active mask t (fun lane => ops.add (a lane) (b lane))
    (cohortAdd p ops row warp active pc a b s) ht
  have add := cohort_add_other p ops row warp active pc t a b s ht
  exact ⟨h.1.trans add.1,h.2.trans add.2⟩

theorem cohort_add_snapshot_run (p : Shape) (repaired : Bool) (ops : Ops α)
    (row warp active pc mask : Nat) (a b : Nat → α) (s : State α)
    (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (h0 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (a lane))
    (h1 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 1 = some (b lane))
    (code : (program repaired)[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (nextCode : (program repaired)[pc+1]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    ((cohortThreads row warp active).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s).bind
      (LarkPartitionCollective.runShuffle (geometry p) (program repaired) (cohortThreads row warp active)) =
      some (followingSnapshot p ops row warp active pc mask a b s) := by
  rw [cohort_add_run p repaired ops row warp active pc mask a b s hw (by omega) hp h0 h1 code nextCode]
  simp only [Option.some_bind]
  exact cohort_xor_shuffle p repaired row warp active mask (pc+1)
    (cohortAdd p ops row warp active pc a b s) (fun lane => ops.add (a lane) (b lane)) hw ha hm
    (fun lane hl => (cohort_add_fields p ops row warp active pc lane a b s hw (by omega) hl).1)
    (fun lane hl => (cohort_add_fields p ops row warp active pc lane a b s hw (by omega) hl).2) nextCode

theorem native_add_snapshot_step (p : Shape) (repaired : Bool) (ops : Ops α)
    (row warp active pc mask n : Nat) (a b : Nat → α) (s : State α)
    (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (h0 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (a lane))
    (h1 : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 1 = some (b lane))
    (code : (program repaired)[pc]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))))
    (nextCode : (program repaired)[pc+1]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp active) (n+1) s =
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp active) n (followingSnapshot p ops row warp active pc mask a b s) := by
  rw [run_warp_continue,cohort_add_run p repaired ops row warp active pc mask a b s hw (by omega) hp h0 h1 code nextCode]
  simp only [Option.some_bind]
  have hn := cohort_next repaired row warp active (pc+1)
    (cohortAdd p ops row warp active pc a b s) (by omega)
    (fun lane hl => (cohort_add_fields p ops row warp active pc lane a b s hw (by omega) hl).1)
    (by intro t ht; simp only [LarkPartitionCollective.isShuffle,ht,nextCode])
  have hs := cohort_xor_shuffle p repaired row warp active mask (pc+1)
    (cohortAdd p ops row warp active pc a b s) (fun lane => ops.add (a lane) (b lane)) hw ha hm
    (fun lane hl => (cohort_add_fields p ops row warp active pc lane a b s hw (by omega) hl).1)
    (fun lane hl => (cohort_add_fields p ops row warp active pc lane a b s hw (by omega) hl).2) nextCode
  unfold continueCohort
  rw [hn]
  dsimp only
  rw [hs]
  rfl

#print axioms cohort_add_fields
#print axioms cohort_add_preserves
#print axioms cohort_add_other
#print axioms cohort_add_run
#print axioms following_snapshot_fields
#print axioms following_snapshot_preserves
#print axioms following_snapshot_other
#print axioms cohort_add_snapshot_run
#print axioms native_add_snapshot_step
end LarkNativeSglangRmsNorm
