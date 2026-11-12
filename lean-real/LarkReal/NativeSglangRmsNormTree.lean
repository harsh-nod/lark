import Lark.NativeSglangRmsNormCorrect
import LarkReal.Ops

/-! The exact-real interpretation of both logical32 XOR reductions. The first
reduction uses the actual lower/upper physical-wave partitions; every lower
logical lane of the second reduction contains each partial exactly once.
-/
namespace LarkReal.NativeSglangRmsNorm
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def tree : Nat → Nat → AddTree
  | 0,lane => .leaf lane
  | k+1,lane => .join (tree k lane) (tree k (xorPeer32 lane (reductionMask k)))

theorem lower_leaves : ∀ lane : Fin 32,(tree 5 lane.val).leaves.Perm (List.range 32) := by decide
theorem upper_leaves : (tree 5 32).leaves.Perm (List.range' 32 32) := by decide

theorem reduction_tree (base : Nat → ℝ) (k lane : Nat) :
    reductionValues ops base k lane=(tree k lane).eval base := by
  induction k generalizing lane with
  | zero => rfl
  | succ k ih =>
      change reductionValues ops base k lane + reductionValues ops base k (xorPeer32 lane (reductionMask k))=_
      rw [ih,ih]
      rfl

theorem reduction_sum32 (base : Nat → ℝ) (lane : Nat) (hl : lane<32) :
    reductionValues ops base 5 lane=((List.range 32).map base).sum := by
  rw [reduction_tree]
  exact tree_permutation (tree 5 lane) (List.range 32) base (lower_leaves ⟨lane,hl⟩)

theorem partial_sum (input : Nat → Nat → ℝ) (row logicalWarp : Nat) :
    blockPartialValue ops input row logicalWarp=
      ((List.range' (logicalWarp*32) 32).map (threadSum ops input row)).sum := by
  unfold blockPartialValue
  rw [reduction_tree]
  change (tree 5 ((logicalWarp%2)*32)).eval (fun l => threadSum ops input row (logicalWarp/2*64+l))=_
  have cases : logicalWarp%2=0 ∨ logicalWarp%2=1 := by omega
  rcases cases with he | he
  · rw [he]
    have h := tree_permutation (tree 5 0) (List.range 32)
      (fun l => threadSum ops input row (logicalWarp/2*64+l)) (lower_leaves ⟨0,by decide⟩)
    simp only [Nat.zero_mul] at *
    rw [h]
    have offset : logicalWarp/2*64=logicalWarp*32 := by omega
    simp [offset,List.range'_eq_map_range,List.map_map,Function.comp_def]
  · rw [he]
    have h := tree_permutation (tree 5 32) (List.range' 32 32)
      (fun l => threadSum ops input row (logicalWarp/2*64+l)) upper_leaves
    simp only [Nat.one_mul] at *
    rw [h]
    have offset : logicalWarp/2*64+32=logicalWarp*32 := by omega
    simp only [List.range'_eq_map_range,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    congr 1
    omega

#print axioms lower_leaves
#print axioms upper_leaves
#print axioms reduction_tree
#print axioms reduction_sum32
#print axioms partial_sum
end LarkReal.NativeSglangRmsNorm
