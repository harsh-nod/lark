import LarkReal.Ops
open LarkReal

example (v : Nat → ℝ) :
    (AddTree.leaf 0).eval v = ([0, 1].map v).sum := by
  exact tree_permutation _ _ v (by decide)
