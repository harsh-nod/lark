import Lark.NativeFusedRmsNormXor

/-! Register-level effects of the actual snapshot update. The old accumulator
is retained, the peer value comes from the snapshot, and memory/epochs/trace do
not change. This applies equally to either logical half of a native wave.
-/
namespace LarkNativeFusedRmsNorm
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

theorem xor_shuffled_fields (p : Shape) (row warp active mask lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (ha : active ≤ 64) (hl : lane < active) :
    let next := shuffleUpdates 1 (xorSnapshot p row warp active mask values) s
    let t := cohortBase row warp + lane
    next.pc t = s.pc t + 1 ∧ next.regs t 0 = s.regs t 0 ∧
      next.regs t 1 = some (values (xorPeer32 lane mask)) := by
  have ht := (cohort_mem row warp active _).mpr ⟨lane, hl, rfl⟩
  dsimp only
  simp only [shuffleUpdates, xorSnapshot, snapshot_any, ht, decide_true, ↓reduceIte]
  rewrite [snapshot_lookup _ _ _ ht, (cohort_coords p row warp lane hw (by omega)).2]
  trivial

theorem xor_shuffled_other (p : Shape) (row warp active mask t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp active) :
    let next := shuffleUpdates 1 (xorSnapshot p row warp active mask values) s
    next.pc t = s.pc t ∧ next.regs t = s.regs t := by
  dsimp only
  constructor
  · simp only [shuffleUpdates, xorSnapshot, snapshot_any, ht, decide_false, Bool.false_eq_true, ↓reduceIte]
  · funext r
    simp only [shuffleUpdates, xorSnapshot]
    split
    · rewrite [snapshot_lookup_other _ _ _ ht]
      rfl
    · rfl

theorem xor_shuffled_preserves (p : Shape) (row warp active mask : Nat)
    (values : Nat → α) (s : State α) :
    let next := shuffleUpdates 1 (xorSnapshot p row warp active mask values) s
    next.memory = s.memory ∧ next.indices = s.indices ∧
      next.epochs = s.epochs ∧ next.trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

theorem native_first_snapshot_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp lane : Nat)
    (hr : row < p.rows) (hw : warp < 16) (hl : lane < 64) :
    let next := shuffleUpdates 1 (xorSnapshot p row warp 64 16
      (fun l => threadSum ops input row (warp * 64 + l)))
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside))
    next.pc (cohortBase row warp + lane) = 24 ∧
      next.regs (cohortBase row warp + lane) 0 = some (threadSum ops input row (warp * 64 + lane)) ∧
      next.regs (cohortBase row warp + lane) 1 =
        some (threadSum ops input row (warp * 64 + xorPeer32 lane 16)) := by
  have h := xor_shuffled_fields p row warp 64 16 lane
    (fun l => threadSum ops input row (warp * 64 + l))
    (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) hw (by decide) hl
  have ready := native_prefix_ready p ops input outside row warp hr hw lane hl
  have coords := cohort_arithmetic row warp lane hw hl
  simpa only [ready.pc, ready.accumulator, coords.1, coords.2.1] using h

#print axioms snapshot_lookup
#print axioms snapshot_any
#print axioms xor_shuffled_fields
#print axioms xor_shuffled_other
#print axioms xor_shuffled_preserves
#print axioms native_first_snapshot_values
end LarkNativeFusedRmsNorm
