import Lark.NativeSglangRmsNormSnapshotAdd
import Lark.NativeSglangRmsNormWaveEntry

/-! All five source XOR snapshots and the first four ordered additions.
The resulting PC53 still precedes the final addition and shared partial store.
The successful prefix and the native runner continuation are proved separately.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold addFold

def reductionMask : Nat → Nat
  | 0 => 16 | 1 => 8 | 2 => 4 | 3 => 2 | _ => 1

def reductionValues (ops : Ops α) (base : Nat → α) : Nat → Nat → α
  | 0, lane => base lane
  | k+1, lane => ops.add (reductionValues ops base k lane)
      (reductionValues ops base k (xorPeer32 lane (reductionMask k)))

def reductionSnapshot (p : Shape) (ops : Ops α) (row warp : Nat)
    (base : Nat → α) (s : State α) : Nat → State α
  | 0 => shuffleUpdates 1 (xorSnapshot p row warp 64 16 base) s
  | k+1 => followingSnapshot p ops row warp 64 (45+2*k) (reductionMask (k+1))
      (reductionValues ops base k)
      (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
      (reductionSnapshot p ops row warp base s k)

theorem reduction_snapshot_fields (p : Shape) (ops : Ops α) (row warp k lane : Nat)
    (base : Nat → α) (s : State α) (hw : warp < 16) (hl : lane < 64)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 44)
    (hr : ∀ lane, lane < 64 → s.regs (cohortBase row warp + lane) 0 = some (base lane)) :
    (reductionSnapshot p ops row warp base s k).pc (cohortBase row warp + lane) = 45+2*k ∧
    (reductionSnapshot p ops row warp base s k).regs (cohortBase row warp + lane) 0 =
      some (reductionValues ops base k lane) ∧
    (reductionSnapshot p ops row warp base s k).regs (cohortBase row warp + lane) 1 =
      some (reductionValues ops base k (xorPeer32 lane (reductionMask k))) := by
  cases k with
  | zero =>
      have h := xor_shuffled_fields p row warp 64 16 lane base s hw (by decide) hl
      exact ⟨by simpa only [hp lane hl] using h.1,h.2.1.trans (hr lane hl),h.2.2⟩
  | succ k =>
      have h := following_snapshot_fields p ops row warp 64 (45+2*k) (reductionMask (k+1)) lane
        (reductionValues ops base k)
        (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (reductionSnapshot p ops row warp base s k) hw (by decide) hl
      have he : 45+2*k+2 = 45+2*(k+1) := by omega
      exact ⟨h.1.trans he,h.2.1,h.2.2⟩

theorem reduction_snapshot_preserves (p : Shape) (ops : Ops α) (row warp k : Nat)
    (base : Nat → α) (s : State α) :
    (reductionSnapshot p ops row warp base s k).memory = s.memory ∧
    (reductionSnapshot p ops row warp base s k).indices = s.indices ∧
    (reductionSnapshot p ops row warp base s k).epochs = s.epochs ∧
    (reductionSnapshot p ops row warp base s k).trace = s.trace := by
  induction k with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ k ih =>
      have h := following_snapshot_preserves p ops row warp 64 (45+2*k) (reductionMask (k+1))
        (reductionValues ops base k)
        (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (reductionSnapshot p ops row warp base s k)
      exact ⟨h.1.trans ih.1,h.2.1.trans ih.2.1,h.2.2.1.trans ih.2.2.1,h.2.2.2.trans ih.2.2.2⟩

theorem reduction_snapshot_other (p : Shape) (ops : Ops α) (row warp k t : Nat)
    (base : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp 64) :
    (reductionSnapshot p ops row warp base s k).pc t = s.pc t ∧
    (reductionSnapshot p ops row warp base s k).regs t = s.regs t := by
  induction k with
  | zero => exact xor_shuffled_other p row warp 64 16 t base s ht
  | succ k ih =>
      have h := following_snapshot_other p ops row warp 64 (45+2*k) (reductionMask (k+1)) t
        (reductionValues ops base k)
        (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (reductionSnapshot p ops row warp base s k) ht
      exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem first_reduction_sites (repaired : Bool) (k : Nat) (hk : k < 4) :
    (program repaired)[45+2*k]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) ∧
    (program repaired)[45+2*k+1]? = some (.shuffle .xor 1 0 (.const (reductionMask (k+1) : Int)) 32) ∧
    reductionMask (k+1) < 32 := by
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> cases repaired <;> decide

def runSnapshotPairs (p : Shape) (repaired : Bool) (ops : Ops α) (row warp : Nat) : Nat → State α → Option (State α)
  | 0, s => some s
  | k+1, s => (runSnapshotPairs p repaired ops row warp k s).bind fun u =>
      ((cohortThreads row warp 64).foldlM
        (fun v t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane v) u).bind
        (LarkPartitionCollective.runShuffle (geometry p) (program repaired) (cohortThreads row warp 64))

theorem snapshot_pairs_success (p : Shape) (repaired : Bool) (ops : Ops α) (row warp k : Nat)
    (base : Nat → α) (s : State α) (hw : warp < 16) (hk : k ≤ 4)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 44)
    (hr : ∀ lane, lane < 64 → s.regs (cohortBase row warp + lane) 0 = some (base lane)) :
    runSnapshotPairs p repaired ops row warp k (reductionSnapshot p ops row warp base s 0) =
      some (reductionSnapshot p ops row warp base s k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [runSnapshotPairs,ih (by omega),Option.some_bind]
      have sites := first_reduction_sites repaired k (by omega)
      exact cohort_add_snapshot_run p repaired ops row warp 64 (45+2*k) (reductionMask (k+1))
        (reductionValues ops base k)
        (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
        (reductionSnapshot p ops row warp base s k) hw (Or.inr rfl) sites.2.2
        (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).1)
        (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).2.1)
        (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).2.2)
        sites.1 sites.2.1

theorem native_reduction_snapshot_step (p : Shape) (repaired : Bool) (ops : Ops α)
    (row warp k n : Nat) (base : Nat → α) (s : State α) (hw : warp < 16) (hk : k < 4)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 44)
    (hr : ∀ lane, lane < 64 → s.regs (cohortBase row warp + lane) 0 = some (base lane)) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) (n+1) (reductionSnapshot p ops row warp base s k) =
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) n (reductionSnapshot p ops row warp base s (k+1)) := by
  have sites := first_reduction_sites repaired k hk
  exact native_add_snapshot_step p repaired ops row warp 64 (45+2*k) (reductionMask (k+1)) n
    (reductionValues ops base k)
    (fun lane => reductionValues ops base k (xorPeer32 lane (reductionMask k)))
    (reductionSnapshot p ops row warp base s k) hw (Or.inr rfl) sites.2.2
    (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).1)
    (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).2.1)
    (fun lane hl => (reduction_snapshot_fields p ops row warp k lane base s hw hl hp hr).2.2)
    sites.1 sites.2.1

theorem native_reduction_four (p : Shape) (repaired : Bool) (ops : Ops α)
    (row warp n : Nat) (base : Nat → α) (s : State α) (hw : warp < 16)
    (hp : ∀ lane, lane < 64 → s.pc (cohortBase row warp + lane) = 44)
    (hr : ∀ lane, lane < 64 → s.regs (cohortBase row warp + lane) 0 = some (base lane)) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) (n+4) (reductionSnapshot p ops row warp base s 0) =
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) n (reductionSnapshot p ops row warp base s 4) := by
  have h0 := native_reduction_snapshot_step p repaired ops row warp 0 (n+3) base s hw (by decide) hp hr
  have h1 := native_reduction_snapshot_step p repaired ops row warp 1 (n+2) base s hw (by decide) hp hr
  have h2 := native_reduction_snapshot_step p repaired ops row warp 2 (n+1) base s hw (by decide) hp hr
  have h3 := native_reduction_snapshot_step p repaired ops row warp 3 n base s hw (by decide) hp hr
  simp only [Nat.add_assoc] at h0 h1 h2
  exact h0.trans (h1.trans (h2.trans h3))

#print axioms reduction_snapshot_fields
#print axioms reduction_snapshot_preserves
#print axioms reduction_snapshot_other
#print axioms first_reduction_sites
#print axioms snapshot_pairs_success
#print axioms native_reduction_snapshot_step
#print axioms native_reduction_four
end LarkNativeSglangRmsNorm
