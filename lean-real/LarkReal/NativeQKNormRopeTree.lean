import Lark.NativeQKNormRopeStages
import LarkReal.Ops

/-! Exact-real interpretation of every native logical-width-32 reduction tree. -/
namespace LarkReal.NativeQKNormRope
open LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def tree : Nat → Nat → AddTree
  | 0, lane => .leaf lane
  | n + 1, lane => .join (tree n lane) (tree n (xorPeer32 lane (xorMask n)))

theorem tree_leaves (lane : Nat) (hl : lane < 64) :
    (tree 5 lane).leaves.Perm (List.range' (lane / 32 * 32) 32) := by
  have all : ∀ l : Fin 64, (tree 5 l.val).leaves.Perm (List.range' (l.val / 32 * 32) 32) := by decide
  exact all ⟨lane, hl⟩

theorem wave_tree (input : Nat → Nat → ℝ) (block warp n lane : Nat) :
    waveValues ops input block warp n lane =
      (tree n lane).eval (fun l => squarePrefix ops input (cohortBase block warp + l) 4) := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih =>
      change waveValues ops input block warp n lane + waveValues ops input block warp n (xorPeer32 lane (xorMask n)) = _
      rw [ih, ih]
      rfl

theorem wave_sum (input : Nat → Nat → ℝ) (block warp lane : Nat) (hl : lane < 64) :
    waveValues ops input block warp 5 lane =
      ((List.range' (lane / 32 * 32) 32).map (fun l => squarePrefix ops input (cohortBase block warp + l) 4)).sum := by
  rw [wave_tree]
  exact tree_permutation (tree 5 lane) _ _ (tree_leaves lane hl)

#print axioms tree_leaves
#print axioms wave_tree
#print axioms wave_sum
end LarkReal.NativeQKNormRope
