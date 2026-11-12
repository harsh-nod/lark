import Lark.NativeQKNormRopeXor

/-! Register effects and exact frames of the actual snapshot update. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem snapshot_lookup (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∈ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = some (values t) := by
  induction ts with
  | nil => simp at ht
  | cons u ts ih =>
      by_cases he : t = u
      · subst t; simp
      · have hm : t ∈ ts := by simpa [he] using ht
        simpa only [List.map_cons, List.lookup_cons, show (t == u) = false by simp [he]] using ih hm

theorem snapshot_lookup_other (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∉ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = none := by
  induction ts with
  | nil => rfl
  | cons u ts ih =>
      have hne : t ≠ u := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      simpa only [List.map_cons, List.lookup_cons, show (t == u) = false by simp [hne]] using ih hn

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

theorem xor_shuffled_fields (p : Shape) (block warp active mask lane dest : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 4) (ha : active ≤ 64) (hl : lane < active) :
    let next := shuffleUpdates dest (xorSnapshot p block warp active mask values) s
    let t := cohortBase block warp + lane
    next.pc t = s.pc t + 1 ∧ next.regs t dest = some (values (xorPeer32 lane mask)) := by
  have ht := (cohort_mem block warp active _).mpr ⟨lane, hl, rfl⟩
  dsimp only
  simp only [shuffleUpdates, xorSnapshot, snapshot_any, ht, decide_true, ↓reduceIte]
  rw [snapshot_lookup _ _ _ ht, (cohort_coords p block warp lane hw (by omega)).2]
  trivial

theorem xor_shuffled_reg (p : Shape) (block warp active mask dest t r : Nat)
    (values : Nat → α) (s : State α) (hr : r ≠ dest) :
    (shuffleUpdates dest (xorSnapshot p block warp active mask values) s).regs t r = s.regs t r := by
  simp [shuffleUpdates, hr]

theorem xor_shuffled_other (p : Shape) (block warp active mask dest t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads block warp active) :
    let next := shuffleUpdates dest (xorSnapshot p block warp active mask values) s
    next.pc t = s.pc t ∧ next.regs t = s.regs t := by
  dsimp only
  constructor
  · simp only [shuffleUpdates, xorSnapshot, snapshot_any, ht, decide_false, Bool.false_eq_true, ↓reduceIte]
  · funext r
    simp only [shuffleUpdates, xorSnapshot]
    split
    · rw [snapshot_lookup_other _ _ _ ht]
    · rfl

theorem xor_shuffled_preserves (p : Shape) (block warp active mask dest : Nat)
    (values : Nat → α) (s : State α) :
    let next := shuffleUpdates dest (xorSnapshot p block warp active mask values) s
    next.memory = s.memory ∧ next.indices = s.indices ∧ next.epochs = s.epochs ∧ next.trace = s.trace :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms snapshot_lookup
#print axioms snapshot_lookup_other
#print axioms snapshot_any
#print axioms xor_shuffled_fields
#print axioms xor_shuffled_reg
#print axioms xor_shuffled_other
#print axioms xor_shuffled_preserves
end LarkNativeQKNormRope
