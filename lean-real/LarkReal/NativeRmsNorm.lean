import Lark.NativeRmsNormCorrect
import LarkReal.Ops

/-! Canonical real RMSNorm and its connection to the complete actual native
launch. The exact-real interpretation does not assert IEEE error bounds.
-/
namespace LarkReal.NativeRmsNorm
open LarkDownReduction LarkNativeRmsNorm
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem balanced_sum (values : Nat → ℝ) (n lane : Nat) :
    balanced (· + ·) values n lane = ((List.range' lane (2 ^ n)).map values).sum := by
  induction n generalizing lane with
  | zero => simp [balanced]
  | succ n ih =>
      rewrite [balanced, ih, ih, ← List.sum_append, ← List.map_append]
      have he := List.range'_append (s := lane) (m := 2 ^ n) (n := 2 ^ n) (step := 1)
      simpa only [Nat.one_mul, Nat.pow_succ, Nat.mul_two] using
        congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem sum_blocks (values : Nat → ℝ) (n width start : Nat) :
    ((List.range n).map (fun block =>
      ((List.range' (start + block * width) width).map values).sum)).sum =
      ((List.range' start (n * width)).map values).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rewrite [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      rewrite [← List.sum_append, ← List.map_append]
      have he := List.range'_append (s := start) (m := n * width) (n := width) (step := 1)
      simpa only [Nat.one_mul, Nat.add_mul, Nat.one_mul] using
        congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem thread_sum (input : Nat → Nat → ℝ) (row tid : Nat) :
    threadSum ops input row tid =
      ((List.range' (tid * 8) 8).map (square ops input row)).sum +
      ((List.range' (8192 + tid * 8) 8).map (square ops input row)).sum := by
  unfold threadSum threadCells
  change List.foldl (fun acc col => acc + square ops input row col) (ops.literal 0 1) _ = _
  rewrite [fold_add]
  have zero : ops.literal 0 1 = (0 : ℝ) := by simp [ops]
  rewrite [zero, zero_add]
  change (((List.range 2).flatMap fun iteration => (List.range 8).map
    (fun component => (tid + iteration * 1024) * 8 + component)).map
    (square ops input row)).sum = _
  have htwo : List.range 2 = [0, 1] := by decide
  simp only [htwo, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append, List.map_map, List.sum_append]
  simp [List.range'_eq_map_range, List.map_map, Function.comp_def,
    Nat.add_mul, Nat.add_comm, Nat.add_left_comm]

theorem warp_sum (input : Nat → Nat → ℝ) (row warp : Nat) (hw : warp < 16) :
    warpSum ops input row warp =
      ((List.range' (warp * 64) 64).map (threadSum ops input row)).sum := by
  rewrite [warp_sum_tree ops input row warp hw]
  change balanced (· + ·) (fun lane => threadSum ops input row (warp * 64 + lane)) 6 0 = _
  rewrite [balanced_sum]
  simp [List.range'_eq_map_range, List.map_map, Function.comp_def]

theorem block_sum (input : Nat → Nat → ℝ) (row : Nat) :
    blockSum ops input row =
      ((List.range 16384).map (square ops input row)).sum := by
  rewrite [block_sum_tree]
  change balanced (· + ·) (warpSum ops input row) 4 0 = _
  rewrite [balanced_sum]
  have hwarps : ((List.range' 0 (2 ^ 4)).map (warpSum ops input row)).sum =
      ((List.range 16).map fun warp =>
        ((List.range' (0 + warp * 64) 64).map (threadSum ops input row)).sum).sum := by
    change ((List.range' 0 16).map (warpSum ops input row)).sum = _
    rewrite [← List.range_eq_range']
    apply congrArg List.sum
    apply List.map_congr_left
    intro warp hw
    simpa only [Nat.zero_add] using warp_sum input row warp (List.mem_range.mp hw)
  rewrite [hwarps, sum_blocks]
  have hthreads : ((List.range' 0 (16 * 64)).map (threadSum ops input row)).sum =
      ((List.range 1024).map fun tid =>
        ((List.range' (0 + tid * 8) 8).map (square ops input row)).sum +
        ((List.range' (8192 + tid * 8) 8).map (square ops input row)).sum).sum := by
    change ((List.range' 0 1024).map (threadSum ops input row)).sum = _
    rewrite [← List.range_eq_range']
    apply congrArg List.sum
    apply List.map_congr_left
    intro tid ht
    simpa only [Nat.zero_add] using thread_sum input row tid
  rewrite [hthreads, List.sum_map_add, sum_blocks, sum_blocks,
    ← List.sum_append, ← List.map_append]
  have he := List.range'_append (s := 0) (m := 8192) (n := 8192) (step := 1)
  simpa only [Nat.zero_add, Nat.one_mul, ← List.range_eq_range'] using
    congrArg (fun xs : List Nat => (xs.map (square ops input row)).sum) he

noncomputable def canonical (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  input 1 (row * 16384 + col) *
    (1 / Real.sqrt ((((List.range 16384).map fun j =>
      input 1 (row * 16384 + j) * input 1 (row * 16384 + j)).sum) / 16384 + 1 / 100000)) *
    input 2 col

/-- Algebraic equivalence of the intended source-phase value to the real reference.
No execution, trace, IEEE accuracy or original-paper reproduction is asserted.
-/
theorem result_eq_canonical (input : Nat → Nat → ℝ) (row col : Nat) :
    result ops input row col = canonical input row col := by
  unfold result scale
  rewrite [block_sum]
  have hterm : LarkNativeRmsNorm.square ops input row =
      fun j => input 1 (row * 16384 + j) * input 1 (row * 16384 + j) := by
    funext j
    rfl
  rewrite [hterm]
  norm_num only [ops, canonical, id_eq]

noncomputable def canonical_spec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows * 16384)).map fun offset => canonical input (offset / 16384) (offset % 16384)

theorem spec_eq (p : Shape) (input : Nat → Nat → ℝ) : spec p ops input = canonical_spec p input := by
  apply List.map_congr_left
  intro offset ho
  exact result_eq_canonical input (offset / 16384) (offset % 16384)

/-- Whole actual native launch, actual-trace race freedom and the canonical real
weighted RMSNorm reference, for all inputs and arbitrary initial outside memory.
The source's fixed shape, aligned host contract and explicit reduction rewrite
remain the scope of this theorem.
-/
theorem correct (p : Shape) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel program (canonical_spec p) := by
  intro input outside
  obtain ⟨final, he, hr, hv⟩ := LarkNativeRmsNorm.correct p ops input outside
  exact ⟨final, he, hr, hv.trans (congrArg some (spec_eq p input))⟩

#print axioms balanced_sum
#print axioms block_sum
#print axioms result_eq_canonical
#print axioms correct
end LarkReal.NativeRmsNorm
