import Lark.NativeFusedRmsNormCorrect
import LarkReal.Ops

/-! Exact-real reference for the complete seeded-inout native fused RMSNorm
launch. The reduction tree is a permutation of every source square; both
normalized and residual buffers match an independently stated formula.
Storage conversions are identities here. No IEEE accuracy bound is asserted.
-/
namespace LarkReal.NativeFusedRmsNorm
open LarkNativeFusedRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def tree : Nat → Nat → AddTree
  | 0, lane => .leaf lane
  | n + 1, lane => .join (tree n lane) (tree n (xorPeer32 lane (xorMask n)))

theorem lower_leaves : (tree 5 0).leaves.Perm (List.range 32) := by decide
theorem upper_leaves : (tree 5 32).leaves.Perm (List.range' 32 32) := by decide

theorem wave_tree (input : Nat → Nat → ℝ) (row warp n lane : Nat) :
    waveValues ops input row warp n lane =
      (tree n lane).eval (fun l => threadSum ops input row (warp * 64 + l)) := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih =>
      change waveValues ops input row warp n lane + waveValues ops input row warp n (xorPeer32 lane (xorMask n)) = _
      rewrite [ih,ih]
      rfl

theorem logical_tree (input : Nat → Nat → ℝ) (row n lane : Nat) :
    logicalValues ops input row n lane = (tree n lane).eval (blockPartial ops input row) := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih =>
      change logicalValues ops input row n lane + logicalValues ops input row n (xorPeer32 lane (xorMask n)) = _
      rewrite [ih,ih]
      rfl

theorem block_partials_sum (input : Nat → Nat → ℝ) (row : Nat) :
    blockSum ops input row = ((List.range 32).map (blockPartial ops input row)).sum := by
  unfold blockSum
  rewrite [logical_tree]
  exact tree_permutation (tree 5 0) (List.range 32) (blockPartial ops input row) lower_leaves

theorem partial_sum (input : Nat → Nat → ℝ) (row logicalWarp : Nat) :
    blockPartial ops input row logicalWarp =
      ((List.range' (logicalWarp * 32) 32).map (threadSum ops input row)).sum := by
  unfold blockPartial
  rewrite [wave_tree]
  have hh : logicalWarp % 2 = 0 ∨ logicalWarp % 2 = 1 := by omega
  rcases hh with hh | hh
  · rewrite [hh]
    have h := tree_permutation (tree 5 0) (List.range 32)
      (fun l => threadSum ops input row (logicalWarp / 2 * 64 + l)) lower_leaves
    simp only [Nat.zero_mul] at *
    rewrite [h]
    have he : logicalWarp / 2 * 64 = logicalWarp * 32 := by omega
    simp [he,List.range'_eq_map_range,List.map_map,Function.comp_def]
  · rewrite [hh]
    have h := tree_permutation (tree 5 32) (List.range' 32 32)
      (fun l => threadSum ops input row (logicalWarp / 2 * 64 + l)) upper_leaves
    simp only [Nat.one_mul] at *
    rewrite [h]
    have he : logicalWarp / 2 * 64 + 32 = logicalWarp * 32 := by omega
    simp only [List.range'_eq_map_range,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    congr 1
    omega

theorem sum_blocks (values : Nat → ℝ) (n width start : Nat) :
    ((List.range n).map (fun block =>
      ((List.range' (start + block * width) width).map values).sum)).sum =
      ((List.range' start (n * width)).map values).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rewrite [List.range_succ,List.map_append,List.sum_append]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
      rewrite [← List.sum_append,← List.map_append]
      have he := List.range'_append (s := start) (m := n * width) (n := width) (step := 1)
      simpa only [Nat.one_mul,Nat.add_mul,Nat.one_mul] using
        congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem folded_sum (input : Nat → Nat → ℝ) (row tid iteration component remaining : Nat) (acc : ℝ) :
    folded ops input row tid iteration component remaining acc =
      acc + ((List.range' component remaining).map (squared ops input row tid iteration)).sum := by
  induction remaining generalizing component acc with
  | zero => simp [folded]
  | succ remaining ih =>
      rewrite [folded,ih,List.range'_succ]
      simp only [List.map_cons,List.sum_cons]
      change (acc + squared ops input row tid iteration component) + _ = _
      exact add_assoc _ _ _

/-- Independent real sum and square of the two original mutable operands. -/
def rowSquare (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  let x := input 0 (row * 16384 + col) + input 1 (row * 16384 + col)
  x * x

theorem squared_eq (input : Nat → Nat → ℝ) (row tid iteration component : Nat) :
    squared ops input row tid iteration component =
      rowSquare input row (column tid iteration component) := by
  rfl

theorem thread_sum (input : Nat → Nat → ℝ) (row tid : Nat) :
    threadSum ops input row tid =
      ((List.range' (tid * 8) 8).map (rowSquare input row)).sum +
      ((List.range' (8192 + tid * 8) 8).map (rowSquare input row)).sum := by
  unfold threadSum
  rewrite [folded_sum,folded_sum]
  have hs (iteration : Nat) : squared ops input row tid iteration =
      fun component => rowSquare input row (column tid iteration component) := by
    funext component
    rfl
  rewrite [hs 0,hs 1]
  simp [ops,List.range'_eq_map_range,List.map_map,Function.comp_def,
    column,Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

theorem block_sum (input : Nat → Nat → ℝ) (row : Nat) :
    blockSum ops input row = ((List.range 16384).map (rowSquare input row)).sum := by
  rewrite [block_partials_sum]
  have hparts : ((List.range 32).map (blockPartial ops input row)).sum =
      ((List.range 32).map fun warp =>
        ((List.range' (0 + warp * 32) 32).map (threadSum ops input row)).sum).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro warp hw
    simpa only [Nat.zero_add] using partial_sum input row warp
  rewrite [hparts,sum_blocks]
  have hthreads : ((List.range' 0 (32 * 32)).map (threadSum ops input row)).sum =
      ((List.range 1024).map fun tid =>
        ((List.range' (0 + tid * 8) 8).map (rowSquare input row)).sum +
        ((List.range' (8192 + tid * 8) 8).map (rowSquare input row)).sum).sum := by
    change ((List.range' 0 1024).map (threadSum ops input row)).sum = _
    rewrite [← List.range_eq_range']
    apply congrArg List.sum
    apply List.map_congr_left
    intro tid ht
    simpa only [Nat.zero_add] using thread_sum input row tid
  rewrite [hthreads,List.sum_map_add,sum_blocks,sum_blocks,
    ← List.sum_append,← List.map_append]
  have he := List.range'_append (s := 0) (m := 8192) (n := 8192) (step := 1)
  simpa only [Nat.zero_add,Nat.one_mul,← List.range_eq_range'] using
    congrArg (fun xs : List Nat => (xs.map (rowSquare input row)).sum) he

/-- The independent normalized real reference, using the original two operands. -/
noncomputable def canonical (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  (input 0 (row * 16384 + col) + input 1 (row * 16384 + col)) *
    (1 / Real.sqrt ((((List.range 16384).map (rowSquare input row)).sum) / 16384 + 1 / 100000)) *
    input 2 col

/-- The second extracted buffer is the original operand sum in the real model. -/
def canonical_residual (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  input 0 (row * 16384 + col) + input 1 (row * 16384 + col)

theorem result_eq_canonical (input : Nat → Nat → ℝ) (row col : Nat) :
    outputResult ops input row col = canonical input row col := by
  unfold outputResult outputWeighted outputInverse
  rewrite [block_sum]
  norm_num only [ops,rowAdded,address,canonical,id_eq,zero_div,zero_add,div_one]

theorem residual_eq_canonical (input : Nat → Nat → ℝ) (row col : Nat) :
    residualResult ops input row col = canonical_residual input row col := by
  rfl

noncomputable def canonical_spec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows * 16384)).map (fun i => canonical input (i / 16384) (i % 16384)) ++
  (List.range (p.rows * 16384)).map (fun i => canonical_residual input (i / 16384) (i % 16384))

theorem spec_eq (p : Shape) (input : Nat → Nat → ℝ) :
    spec p ops input = canonical_spec p input := by
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro offset ho
    exact result_eq_canonical input (offset / 16384) (offset % 16384)
  · apply List.map_congr_left
    intro offset ho
    exact residual_eq_canonical input (offset / 16384) (offset % 16384)

/-- All rows of the actual seeded-inout native launch terminate, its actual trace
is race-free, and extraction of both buffers equals the independent real reference.
This is the exact-real interpretation of the fixed native source family.
-/
theorem correct (p : Shape) :
    LarkInOutPartition.Correct ops (layout p) mutableBuffers (geometry p) fuel program
      (canonical_spec p) := by
  have h := LarkNativeFusedRmsNorm.correct p ops
  refine ⟨h.1,?_⟩
  intro input outside
  obtain ⟨final,he,hr,hv⟩ := h.2 input outside
  exact ⟨final,he,hr,hv.trans (congrArg some (spec_eq p input))⟩

#print axioms wave_tree
#print axioms logical_tree
#print axioms block_partials_sum
#print axioms partial_sum
#print axioms folded_sum
#print axioms sum_blocks
#print axioms squared_eq
#print axioms thread_sum
#print axioms block_sum
#print axioms result_eq_canonical
#print axioms residual_eq_canonical
#print axioms spec_eq
#print axioms correct
end LarkReal.NativeFusedRmsNorm
