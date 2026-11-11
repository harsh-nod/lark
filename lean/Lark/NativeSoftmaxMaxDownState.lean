import Lark.NativeSoftmaxMaxDown

/-! Register-level effects of the actual snapshot update. The old accumulator
is retained, the peer value comes from the snapshot, and memory/epochs/trace do
not change. This applies equally to either logical half of a native wave.
-/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem snapshot_lookup (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∈ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = some (values t) := by
  induction ts with
  | nil => simp at ht
  | cons a ts ih =>
      by_cases he : t = a
      · subst t; simp
      · have hm : t ∈ ts := by simpa [he] using ht
        have hb : (t == a) = false := by simp [he]
        simpa only [List.map_cons, List.lookup_cons, hb] using ih hm

theorem snapshot_lookup_other (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∉ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = none := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
      have hne : t ≠ a := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      simpa only [List.map_cons, List.lookup_cons, show (t == a) = false by simp [hne]] using ih hn

theorem snapshot_any (ts : List Nat) (values : Nat → α) (t : Nat) :
    (ts.map (fun u => (u, values u))).any (fun pair => pair.1 == t) = decide (t ∈ ts) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨pair, hm, he⟩ := List.any_eq_true.mp h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    have he : u = t := by simpa only [beq_iff_eq] using he
    exact he ▸ hu
  · intro ht
    exact List.any_eq_true.mpr ⟨(t, values t), List.mem_map.mpr ⟨t, ht, rfl⟩, by simp⟩

theorem down_shuffled_fields (p : Shape) (row warp active distance lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    let next := shuffleUpdates 2 (downSnapshot p row warp active distance values) s
    let t := cohortBase row warp + lane
    next.pc t = s.pc t + 1 ∧ next.regs t 0 = s.regs t 0 ∧
      next.regs t 2 = some (values (downPeer32 lane distance)) := by
  have ht := (cohort_mem row warp active _).mpr ⟨lane, hl, rfl⟩
  dsimp only
  simp only [shuffleUpdates, downSnapshot, snapshot_any, ht, decide_true, ↓reduceIte]
  rewrite [snapshot_lookup _ _ _ ht, (cohort_coords p row warp lane hw (by omega)).2]
  trivial

theorem down_shuffled_other (p : Shape) (row warp active distance t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    let next := shuffleUpdates 2 (downSnapshot p row warp active distance values) s
    next.pc t = s.pc t ∧ next.regs t = s.regs t := by
  dsimp only
  constructor
  · simp only [shuffleUpdates, downSnapshot, snapshot_any, ht, decide_false, Bool.false_eq_true, ↓reduceIte]
  · funext r
    simp only [shuffleUpdates, downSnapshot]
    split
    · rewrite [snapshot_lookup_other _ _ _ ht]
      rfl
    · rfl

theorem down_shuffled_preserves (p : Shape) (row warp active distance : Nat)
    (values : Nat → α) (s : State α) :
    let next := shuffleUpdates 2 (downSnapshot p row warp active distance values) s
    next.memory = s.memory ∧ next.indices = s.indices ∧
      next.epochs = s.epochs ∧ next.trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

#print axioms snapshot_lookup
#print axioms snapshot_lookup_other
#print axioms snapshot_any
#print axioms down_shuffled_fields
#print axioms down_shuffled_other
#print axioms down_shuffled_preserves
end LarkNativeSoftmax
