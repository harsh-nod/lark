import Lark.WaveSum
import LarkReal.Ops
import Mathlib.Data.Nat.Bitwise

/-! Canonical real sum for the actual six-stage XOR reduction launch. -/
namespace LarkReal.WaveSum
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

def tree : Nat → Nat → AddTree
  | 0, t => .leaf t
  | n + 1, t => .join (tree n t)
      (tree n (Nat.xor t (LarkCollective.WaveSum.distance n)))

theorem value_eq_eval (input : Nat → Nat → ℝ) (n t : Nat) :
    LarkCollective.WaveSum.value LarkReal.ops input n t = (tree n t).eval (input 0) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      change LarkReal.ops.add (LarkCollective.WaveSum.value LarkReal.ops input n t)
        (LarkCollective.WaveSum.value LarkReal.ops input n
          (Nat.xor t (LarkCollective.WaveSum.distance n))) =
        (tree n t).eval (input 0) +
          (tree n (Nat.xor t (LarkCollective.WaveSum.distance n))).eval (input 0)
      rewrite [ih t, ih (Nat.xor t (LarkCollective.WaveSum.distance n))]
      rfl

theorem leaves_shift (n t : Nat) :
    (tree n t).leaves = (tree n 0).leaves.map (Nat.xor t) := by
  induction n generalizing t with
  | zero =>
      change [t] = [Nat.xor t 0]
      exact congrArg (fun x => [x]) (Nat.xor_zero t).symm
  | succ n ih =>
      calc
        (tree (n + 1) t).leaves =
            (tree n 0).leaves.map (Nat.xor t) ++
            (tree n 0).leaves.map (Nat.xor (Nat.xor t (LarkCollective.WaveSum.distance n))) :=
          congrArg₂ List.append (ih t) (ih (Nat.xor t (LarkCollective.WaveSum.distance n)))
        _ = ((tree n 0).leaves ++
            (tree n 0).leaves.map (Nat.xor (LarkCollective.WaveSum.distance n))).map (Nat.xor t) := by
          simp only [List.map_append, List.map_map]
          apply congrArg (List.append ((tree n 0).leaves.map (Nat.xor t)))
          apply List.map_congr_left
          intro x hx
          exact Nat.xor_assoc _ _ _
        _ = (tree (n + 1) 0).leaves.map (Nat.xor t) := by
          apply congrArg (List.map (Nat.xor t))
          change (tree n 0).leaves ++ (tree n 0).leaves.map (Nat.xor (LarkCollective.WaveSum.distance n)) =
            (tree n 0).leaves ++ (tree n (Nat.xor 0 (LarkCollective.WaveSum.distance n))).leaves
          apply congrArg (List.append (tree n 0).leaves)
          have hz : Nat.xor 0 (LarkCollective.WaveSum.distance n) =
              LarkCollective.WaveSum.distance n := Nat.zero_xor _
          rewrite [hz]
          exact (ih (LarkCollective.WaveSum.distance n)).symm

theorem zero_leaves : (tree 6 0).leaves.Perm (List.range 64) := by decide

theorem xor_bound : ∀ t u : Fin 64, Nat.xor t.val u.val < 64 := by decide

theorem xor_range (t : Nat) (ht : t < 64) :
    ((List.range 64).map (Nat.xor t)).Perm (List.range 64) := by
  apply (List.perm_ext_iff_of_nodup
    (((show (List.range 64).Nodup from List.nodup_range)).map (Nat.xor_right_injective (n := t))) ((show (List.range 64).Nodup from List.nodup_range))).mpr
  intro x
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    exact List.mem_range.mpr (xor_bound ⟨t, ht⟩ ⟨u, List.mem_range.mp hu⟩)
  · intro h
    have hx : x < 64 := List.mem_range.mp h
    exact List.mem_map.mpr ⟨Nat.xor t x, List.mem_range.mpr (xor_bound ⟨t, ht⟩ ⟨x, hx⟩),
      Nat.xor_cancel_left t x⟩

/-- Every lane's tree contains each of the 64 input cells exactly once. -/
theorem tree_leaves (t : Fin 64) : (tree 6 t.val).leaves.Perm (List.range 64) := by
  rewrite [leaves_shift]
  exact (zero_leaves.map (Nat.xor t.val)).trans (xor_range t.val t.isLt)

theorem value_eq_sum (input : Nat → Nat → ℝ) (t : Nat) (ht : t < 64) :
    LarkCollective.WaveSum.value LarkReal.ops input 6 t =
      ((List.range 64).map (input 0)).sum := by
  rewrite [value_eq_eval]
  exact tree_permutation (tree 6 t) (List.range 64) (input 0) (tree_leaves ⟨t, ht⟩)

noncomputable def spec (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range 64).map fun _ => ((List.range 64).map (input 0)).sum

theorem spec_eq (input : Nat → Nat → ℝ) :
    LarkCollective.WaveSum.spec LarkReal.ops input = spec input := by
  unfold LarkCollective.WaveSum.spec spec
  apply List.map_congr_left
  intro t ht
  exact value_eq_sum input t (List.mem_range.mp ht)

/-- Full successful launch, RF, all output cells and arbitrary initial outside memory. -/
theorem correct :
    LarkCollective.Correct LarkReal.ops LarkCollective.WaveSum.layout
      LarkCollective.WaveSum.geometry LarkCollective.WaveSum.fuel
      LarkCollective.WaveSum.program spec := by
  have he : LarkCollective.WaveSum.spec LarkReal.ops = spec := by
    funext input
    exact spec_eq input
  rewrite [← he]
  exact LarkCollective.WaveSum.correct LarkReal.ops

#print axioms tree_leaves
#print axioms value_eq_sum
#print axioms correct
end LarkReal.WaveSum
