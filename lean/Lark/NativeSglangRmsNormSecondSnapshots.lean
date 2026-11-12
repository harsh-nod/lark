import Lark.NativeSglangRmsNormMixedCohort
import Lark.NativeSglangRmsNormRegisterAdd

/-! All five second-reduction snapshots and the first four ordered additions.
Every scheduler step retains the full physical64 thread list; only logical32
lanes shuffle and add. The other32 lanes stay parked at PC76 throughout.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold

def secondAdd (p : Shape) (ops : Ops α) (row pc : Nat) (a b : Nat → α) (s : State α) : State α :=
  regAddFold ops 7 pc
    (fun t => a (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => b (LarkPartitionCollective.nativeLane (geometry p) t)) (cohortThreads row 0 32) s

theorem second_add_fields (p : Shape) (ops : Ops α) (row pc lane : Nat)
    (a b : Nat → α) (s : State α) (hl : lane<32) :
    (secondAdd p ops row pc a b s).pc (cohortBase row 0+lane)=pc+1 ∧
    (secondAdd p ops row pc a b s).regs (cohortBase row 0+lane) 7=some (ops.add (a lane) (b lane)) := by
  have h := reg_add_fold_member ops 7 pc
    (fun t => a (LarkPartitionCollective.nativeLane (geometry p) t))
    (fun t => b (LarkPartitionCollective.nativeLane (geometry p) t)) _ s (cohort_nodup row 0 32)
    _ ((cohort_mem row 0 32 _).mpr ⟨lane,hl,rfl⟩)
  simpa only [secondAdd,(cohort_coords p row 0 lane (by decide) (by omega)).2] using h

theorem second_add_other (p : Shape) (ops : Ops α) (row pc t : Nat)
    (a b : Nat → α) (s : State α) (ht : t∉cohortThreads row 0 32) :
    (secondAdd p ops row pc a b s).pc t=s.pc t ∧
    (secondAdd p ops row pc a b s).regs t=s.regs t :=
  reg_add_fold_other ops 7 pc _ _ _ t s ht

theorem second_add_preserves (p : Shape) (ops : Ops α) (row pc : Nat)
    (a b : Nat → α) (s : State α) :
    (secondAdd p ops row pc a b s).memory=s.memory ∧
    (secondAdd p ops row pc a b s).indices=s.indices ∧
    (secondAdd p ops row pc a b s).epochs=s.epochs ∧ (secondAdd p ops row pc a b s).trace=s.trace :=
  reg_add_fold_preserves ops 7 pc _ _ _ s

theorem cohort_upper_excluded (row lane : Nat) :
    cohortBase row 0+32+lane∉cohortThreads row 0 32 := by
  intro ht
  obtain ⟨l,hl,he⟩ := (cohort_mem row 0 32 _).mp ht
  omega

theorem second_add_full_fold (p : Shape) (ops : Ops α) (row pc mask : Nat)
    (a b : Nat → α) (s : State α)
    (hp : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=pc)
    (h7 : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 7=some (a lane))
    (h8 : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 8=some (b lane))
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76)
    (code : (program true)[pc]?=some (.scalar (.assign 7 (.bin .add (.reg 7) (.reg 8)))))
    (nextCode : (program true)[pc+1]?=some (.shuffle .xor 8 7 (.const (mask : Int)) 32)) :
    (cohortThreads row 0 64).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (secondAdd p ops row pc a b s) := by
  have hrun : (cohortThreads row 0 32).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (secondAdd p ops row pc a b s) := by
    apply reg_add_fold_run p ops 7 8 pc mask _ _ _ s (cohort_nodup row 0 32)
    · intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
      exact hp lane hl
    · intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
      simpa only [(cohort_coords p row 0 lane (by decide) (by omega)).2] using h7 lane hl
    · intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row 0 32 t).mp ht
      simpa only [(cohort_coords p row 0 lane (by decide) (by omega)).2] using h8 lane hl
    · exact code
    · exact nextCode
  rw [cohort_split,List.foldlM_append,hrun]
  apply barrier_lane_fold p ops
  intro t ht
  obtain ⟨lane,hl,rfl⟩ := (cohort_upper_mem row 0 t).mp ht
  exact (second_add_other p ops row pc _ a b s (cohort_upper_excluded row lane)).1.trans (inactive lane hl)

def secondFollowing (p : Shape) (ops : Ops α) (row pc mask : Nat)
    (a b : Nat → α) (s : State α) : State α :=
  shuffleUpdates 8 (xorSnapshot p row 0 32 mask (fun lane => ops.add (a lane) (b lane)))
    (secondAdd p ops row pc a b s)

theorem second_following_fields (p : Shape) (ops : Ops α) (row pc mask lane : Nat)
    (a b : Nat → α) (s : State α) (hl : lane<32) :
    (secondFollowing p ops row pc mask a b s).pc (cohortBase row 0+lane)=pc+2 ∧
    (secondFollowing p ops row pc mask a b s).regs (cohortBase row 0+lane) 7=some (ops.add (a lane) (b lane)) ∧
    (secondFollowing p ops row pc mask a b s).regs (cohortBase row 0+lane) 8=
      some (ops.add (a (xorPeer32 lane mask)) (b (xorPeer32 lane mask))) := by
  have ha := second_add_fields p ops row pc lane a b s hl
  have hx := reg_xor_shuffled_fields p row 0 32 mask lane 8 7 (fun lane => ops.add (a lane) (b lane))
    (secondAdd p ops row pc a b s) (by decide) (by decide) hl (by decide)
  exact ⟨by simpa only [ha.1,Nat.add_assoc] using hx.1,hx.2.1.trans ha.2,hx.2.2⟩

theorem second_following_other (p : Shape) (ops : Ops α) (row pc mask t : Nat)
    (a b : Nat → α) (s : State α) (ht : t∉cohortThreads row 0 32) :
    (secondFollowing p ops row pc mask a b s).pc t=s.pc t ∧
    (secondFollowing p ops row pc mask a b s).regs t=s.regs t := by
  have hx := reg_xor_shuffled_other p row 0 32 mask 8 t (fun lane => ops.add (a lane) (b lane))
    (secondAdd p ops row pc a b s) ht
  have ha := second_add_other p ops row pc t a b s ht
  exact ⟨hx.1.trans ha.1,hx.2.trans ha.2⟩

theorem second_following_preserves (p : Shape) (ops : Ops α) (row pc mask : Nat)
    (a b : Nat → α) (s : State α) :
    (secondFollowing p ops row pc mask a b s).memory=s.memory ∧
    (secondFollowing p ops row pc mask a b s).indices=s.indices ∧
    (secondFollowing p ops row pc mask a b s).epochs=s.epochs ∧
    (secondFollowing p ops row pc mask a b s).trace=s.trace :=
  second_add_preserves p ops row pc a b s

theorem native_second_add_step (p : Shape) (ops : Ops α) (row pc mask n : Nat)
    (a b : Nat → α) (s : State α) (hne : pc+1≠76) (hm : mask<32)
    (hp : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=pc)
    (h7 : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 7=some (a lane))
    (h8 : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 8=some (b lane))
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76)
    (code : (program true)[pc]?=some (.scalar (.assign 7 (.bin .add (.reg 7) (.reg 8)))))
    (nextCode : (program true)[pc+1]?=some (.shuffle .xor 8 7 (.const (mask : Int)) 32)) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) (n+1) s=
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) n (secondFollowing p ops row pc mask a b s) := by
  rw [run_warp_continue,second_add_full_fold p ops row pc mask a b s hp h7 h8 inactive code nextCode]
  simp only [Option.some_bind]
  have hn := mixed_next row (pc+1) (secondAdd p ops row pc a b s) hne
    (fun lane hl => (second_add_fields p ops row pc lane a b s hl).1)
    (fun lane hl => (second_add_other p ops row pc _ a b s (cohort_upper_excluded row lane)).1.trans (inactive lane hl))
    (by intro t ht; simp only [LarkPartitionCollective.isShuffle,ht,nextCode])
  have hs := cohort_reg_xor_shuffle p true row 0 32 mask (pc+1) 8 7 (secondAdd p ops row pc a b s)
    (fun lane => ops.add (a lane) (b lane)) (by decide) (Or.inl rfl) hm
    (fun lane hl => (second_add_fields p ops row pc lane a b s hl).1)
    (fun lane hl => (second_add_fields p ops row pc lane a b s hl).2) nextCode
  unfold continueCohort
  rw [hn]
  dsimp only
  rw [hs]
  rfl

def secondSnapshot (p : Shape) (ops : Ops α) (row : Nat) (base : Nat → α) (s : State α) : Nat → State α
  | 0 => shuffleUpdates 8 (xorSnapshot p row 0 32 16 base) s
  | k+1 => secondFollowing p ops row (63+2*k) (reductionMask (k+1))
      (reductionValues ops base k) (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
      (secondSnapshot p ops row base s k)

theorem second_snapshot_fields (p : Shape) (ops : Ops α) (row k lane : Nat)
    (base : Nat → α) (s : State α) (hl : lane<32)
    (hp : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=62)
    (hr : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 7=some (base lane)) :
    (secondSnapshot p ops row base s k).pc (cohortBase row 0+lane)=63+2*k ∧
    (secondSnapshot p ops row base s k).regs (cohortBase row 0+lane) 7=some (reductionValues ops base k lane) ∧
    (secondSnapshot p ops row base s k).regs (cohortBase row 0+lane) 8=
      some (reductionValues ops base k (xorPeer32 lane (reductionMask k))) := by
  cases k with
  | zero =>
      have hx := reg_xor_shuffled_fields p row 0 32 16 lane 8 7 base s (by decide) (by decide) hl (by decide)
      exact ⟨by simpa only [hp lane hl] using hx.1,hx.2.1.trans (hr lane hl),hx.2.2⟩
  | succ k =>
      have h := second_following_fields p ops row (63+2*k) (reductionMask (k+1)) lane
        (reductionValues ops base k) (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (secondSnapshot p ops row base s k) hl
      exact ⟨h.1.trans (by omega),h.2.1,h.2.2⟩

theorem second_snapshot_other (p : Shape) (ops : Ops α) (row k t : Nat)
    (base : Nat → α) (s : State α) (ht : t∉cohortThreads row 0 32) :
    (secondSnapshot p ops row base s k).pc t=s.pc t ∧
    (secondSnapshot p ops row base s k).regs t=s.regs t := by
  induction k with
  | zero => exact reg_xor_shuffled_other p row 0 32 16 8 t base s ht
  | succ k ih =>
      have h := second_following_other p ops row (63+2*k) (reductionMask (k+1)) t
        (reductionValues ops base k) (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (secondSnapshot p ops row base s k) ht
      exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem second_snapshot_preserves (p : Shape) (ops : Ops α) (row k : Nat) (base : Nat → α) (s : State α) :
    (secondSnapshot p ops row base s k).memory=s.memory ∧
    (secondSnapshot p ops row base s k).indices=s.indices ∧
    (secondSnapshot p ops row base s k).epochs=s.epochs ∧
    (secondSnapshot p ops row base s k).trace=s.trace := by
  induction k with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ k ih =>
      have h := second_following_preserves p ops row (63+2*k) (reductionMask (k+1))
        (reductionValues ops base k) (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (secondSnapshot p ops row base s k)
      exact ⟨h.1.trans ih.1,h.2.1.trans ih.2.1,h.2.2.1.trans ih.2.2.1,h.2.2.2.trans ih.2.2.2⟩

theorem second_reduction_sites (k : Nat) (hk : k<4) :
    (program true)[63+2*k]?=some (.scalar (.assign 7 (.bin .add (.reg 7) (.reg 8)))) ∧
    (program true)[63+2*k+1]?=some (.shuffle .xor 8 7 (.const (reductionMask (k+1) : Int)) 32) ∧
    reductionMask (k+1)<32 := by
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

theorem native_second_snapshot_step (p : Shape) (ops : Ops α) (row k n : Nat)
    (base : Nat → α) (s : State α) (hk : k<4)
    (hp : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=62)
    (hr : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 7=some (base lane))
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) (n+1) (secondSnapshot p ops row base s k)=
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) n (secondSnapshot p ops row base s (k+1)) := by
  have sites := second_reduction_sites k hk
  exact native_second_add_step p ops row (63+2*k) (reductionMask (k+1)) n
    (reductionValues ops base k) (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
    (secondSnapshot p ops row base s k) (by omega) sites.2.2
    (fun lane hl => (second_snapshot_fields p ops row k lane base s hl hp hr).1)
    (fun lane hl => (second_snapshot_fields p ops row k lane base s hl hp hr).2.1)
    (fun lane hl => (second_snapshot_fields p ops row k lane base s hl hp hr).2.2)
    (fun lane hl => (second_snapshot_other p ops row k _ base s (cohort_upper_excluded row lane)).1.trans (inactive lane hl))
    sites.1 sites.2.1

theorem native_second_four (p : Shape) (ops : Ops α) (row n : Nat) (base : Nat → α) (s : State α)
    (hp : ∀ lane,lane<32 → s.pc (cohortBase row 0+lane)=62)
    (hr : ∀ lane,lane<32 → s.regs (cohortBase row 0+lane) 7=some (base lane))
    (inactive : ∀ lane,lane<32 → s.pc (cohortBase row 0+32+lane)=76) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) (n+4) (secondSnapshot p ops row base s 0)=
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads row 0 64) n (secondSnapshot p ops row base s 4) := by
  have h0 := native_second_snapshot_step p ops row 0 (n+3) base s (by decide) hp hr inactive
  have h1 := native_second_snapshot_step p ops row 1 (n+2) base s (by decide) hp hr inactive
  have h2 := native_second_snapshot_step p ops row 2 (n+1) base s (by decide) hp hr inactive
  have h3 := native_second_snapshot_step p ops row 3 n base s (by decide) hp hr inactive
  simp only [Nat.add_assoc] at h0 h1 h2
  exact h0.trans (h1.trans (h2.trans h3))

#print axioms second_add_fields
#print axioms second_add_other
#print axioms second_add_preserves
#print axioms cohort_upper_excluded
#print axioms second_add_full_fold
#print axioms second_following_fields
#print axioms second_following_other
#print axioms second_following_preserves
#print axioms native_second_add_step
#print axioms second_snapshot_fields
#print axioms second_snapshot_other
#print axioms second_snapshot_preserves
#print axioms second_reduction_sites
#print axioms native_second_snapshot_step
#print axioms native_second_four
end LarkNativeSglangRmsNorm
