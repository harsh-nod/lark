import LarkReal.NativeSoftmaxScalar

/-! The actual five-stage logical32 XOR trees and serial32 source fold equal
the sum of all1024 thread contributions over reals. Permutations are proved
for the source's two stored leaders; no reassociation is granted to generic Ops. -/
namespace LarkReal.NativeSoftmax
open LarkNonlinear LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sumTree : Nat → Nat → AddTree
  | 0,lane => .leaf lane
  | n+1,lane => .join (sumTree n lane) (sumTree n (sumXorPeer32 lane (sumDistance n)))

theorem wave_value_tree (seed : ℝ) (input : Nat → Nat → ℝ) (row warp n lane : Nat) :
    sumWaveValues (softmaxOps seed) input row warp n lane=
      (sumTree n lane).eval (fun l => threadExpSum (softmaxOps seed) input row (warp*64+l)) := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih =>
    change (softmaxOps seed).add (sumWaveValues (softmaxOps seed) input row warp n lane)
      (sumWaveValues (softmaxOps seed) input row warp n (sumXorPeer32 lane (sumDistance n)))=
      (sumTree n lane).eval (fun l => threadExpSum (softmaxOps seed) input row (warp*64+l))+
      (sumTree n (sumXorPeer32 lane (sumDistance n))).eval (fun l => threadExpSum (softmaxOps seed) input row (warp*64+l))
    rewrite [ih lane,ih (sumXorPeer32 lane (sumDistance n))]
    rfl

theorem leader_tree_leaves (half : Nat) (hh : half<2) :
    (sumTree 5 (half*32)).leaves.Perm (List.range' (half*32) 32) := by
  rcases (show half=0 ∨ half=1 by omega) with rfl | rfl <;> decide

theorem wave_sum_real (seed : ℝ) (input : Nat → Nat → ℝ) (row warp half : Nat) (hh : half<2) :
    sumWaveValues (softmaxOps seed) input row warp 5 (half*32)=
      ((List.range' (half*32) 32).map fun lane => threadExpSum (softmaxOps seed) input row (warp*64+lane)).sum := by
  rewrite [wave_value_tree]
  exact tree_permutation (sumTree 5 (half*32)) (List.range' (half*32) 32)
    (fun lane => threadExpSum (softmaxOps seed) input row (warp*64+lane)) (leader_tree_leaves half hh)

theorem partial_sum_real (seed : ℝ) (input : Nat → Nat → ℝ) (row logical : Nat) :
    expBlockPartial (softmaxOps seed) input row logical=
      ((List.range' (logical*32) 32).map (threadExpSum (softmaxOps seed) input row)).sum := by
  unfold expBlockPartial
  rewrite [wave_sum_real seed input row (logical/2) (logical%2) (Nat.mod_lt _ (by decide))]
  simp only [List.range'_eq_map_range,List.map_map,Function.comp_def,Nat.one_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro lane hl
  congr 1
  omega

theorem serial_fold_real (seed : ℝ) (values : Nat → ℝ) (start count : Nat) (acc : ℝ) :
    sumSerialFold (softmaxOps seed) values start count acc=acc+((List.range' start count).map values).sum := by
  induction count generalizing start acc with
  | zero => simp [sumSerialFold]
  | succ count ih =>
    simp only [sumSerialFold,List.range'_succ,List.map_cons,List.sum_cons]
    rewrite [ih]
    exact add_assoc _ _ _

theorem serial_total_real (seed : ℝ) (values : Nat → ℝ) :
    sumSerialTotal (softmaxOps seed) values=((List.range 32).map values).sum := by
  unfold sumSerialTotal
  rewrite [serial_fold_real]
  have hr : List.range 32=0::List.range' 1 31 := by
    rewrite [List.range_eq_range']
    exact List.range'_succ
  rewrite [hr]
  rfl

theorem real_sum_blocks (values : Nat → ℝ) (n width start : Nat) :
    ((List.range n).map (fun block => ((List.range' (start+block*width) width).map values).sum)).sum=
      ((List.range' start (n*width)).map values).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rewrite [List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
    rewrite [←List.sum_append,←List.map_append]
    have he := List.range'_append (s := start) (m := n*width) (n := width) (step := 1)
    simpa only [Nat.one_mul,Nat.add_mul,Nat.one_mul] using congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem row_sum_threads_real (seed : ℝ) (input : Nat → Nat → ℝ) (row : Nat) :
    rowExpSum (softmaxOps seed) input row=((List.range 1024).map (threadExpSum (softmaxOps seed) input row)).sum := by
  unfold rowExpSum
  rewrite [serial_total_real]
  have he : (List.range 32).map (expBlockPartial (softmaxOps seed) input row)=
      (List.range 32).map (fun logical => ((List.range' (0+logical*32) 32).map (threadExpSum (softmaxOps seed) input row)).sum) := by
    apply List.map_congr_left
    intro logical hl
    simpa only [Nat.zero_add] using partial_sum_real seed input row logical
  rewrite [he,real_sum_blocks]
  rewrite [←List.range_eq_range']
  rfl

#print axioms wave_value_tree
#print axioms leader_tree_leaves
#print axioms wave_sum_real
#print axioms partial_sum_real
#print axioms serial_fold_real
#print axioms serial_total_real
#print axioms real_sum_blocks
#print axioms row_sum_threads_real
end LarkReal.NativeSoftmax
