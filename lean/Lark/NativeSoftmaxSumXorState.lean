import Lark.NativeSoftmaxSumXor

/-! Register-level effects of the actual snapshot update. The old accumulator
is retained, the peer value comes from the snapshot, and memory/epochs/trace do
not change. This applies equally to either logical half of a native wave.
-/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem sum_xor_shuffled_fields (p : Shape) (row warp active distance lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    let next := shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s
    let t := cohortBase row warp + lane
    next.pc t = s.pc t + 1 ∧ next.regs t 6 = s.regs t 6 ∧
      next.regs t 9 = some (values (sumXorPeer32 lane distance)) := by
  have ht := (cohort_mem row warp active _).mpr ⟨lane, hl, rfl⟩
  dsimp only
  simp only [shuffleUpdates, sumXorSnapshot, snapshot_any, ht, decide_true, ↓reduceIte]
  rewrite [snapshot_lookup _ _ _ ht, (cohort_coords p row warp lane hw (by omega)).2]
  trivial

theorem sum_xor_shuffled_other (p : Shape) (row warp active distance t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    let next := shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s
    next.pc t = s.pc t ∧ next.regs t = s.regs t := by
  dsimp only
  constructor
  · simp only [shuffleUpdates, sumXorSnapshot, snapshot_any, ht, decide_false, Bool.false_eq_true, ↓reduceIte]
  · funext r
    simp only [shuffleUpdates, sumXorSnapshot]
    split
    · rewrite [snapshot_lookup_other _ _ _ ht]
      rfl
    · rfl

theorem sum_xor_shuffled_preserves (p : Shape) (row warp active distance : Nat)
    (values : Nat → α) (s : State α) :
    let next := shuffleUpdates 9 (sumXorSnapshot p row warp active distance values) s
    next.memory = s.memory ∧ next.indices = s.indices ∧
      next.epochs = s.epochs ∧ next.trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩


#print axioms sum_xor_shuffled_fields
#print axioms sum_xor_shuffled_other
#print axioms sum_xor_shuffled_preserves
end LarkNativeSoftmax
