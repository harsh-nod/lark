import Lark.NativeRmsNormProgram
import Lark.DownReduction

/-! Exact expression-tree target for the native source. It is a specification
of the intended source phases; execution equivalence is a separate obligation.+-/
namespace LarkNativeRmsNorm
open LarkNonlinear LarkDownReduction

def threadCells (tid : Nat) : List Nat :=
  (List.range 2).flatMap fun iteration =>
    (List.range 8).map fun component => (tid + iteration * 1024) * 8 + component

def square (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  let x := ops.fromHalf (input 1 (row * 16384 + col))
  ops.mul x x

def threadSum (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) : α :=
  (threadCells tid).foldl (fun acc col => ops.add acc (square ops input row col)) (ops.literal 0 1)

def warpSum (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) : α :=
  reduced ops.add 64 (1024 - warp * 64)
    (fun lane => threadSum ops input row (warp * 64 + lane)) 6 0

def blockSum (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : α :=
  reduced ops.add 16 16 (warpSum ops input row) 4 0

def scale (ops : Ops α) (input : Nat → Nat → α) (row : Nat) : α :=
  ops.rsqrt (ops.add (ops.div (blockSum ops input row) (ops.literal 16384 1))
    (ops.literal 1 100000))

def result (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.mul (ops.mul (ops.fromHalf (input 1 (row * 16384 + col)))
    (scale ops input row)) (ops.fromHalf (input 2 col)))

def spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * 16384)).map fun offset =>
    result ops input (offset / 16384) (offset % 16384)

theorem warp_valid (warp : Nat) (hw : warp < 16) : 64 ≤ 1024 - warp * 64 := by omega

theorem warp_sum_tree (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat)
    (hw : warp < 16) :
    warpSum ops input row warp =
      balanced ops.add (fun lane => threadSum ops input row (warp * 64 + lane)) 6 0 :=
  wave64_lane_zero _ _ _ (warp_valid warp hw)

theorem block_sum_tree (ops : Ops α) (input : Nat → Nat → α) (row : Nat) :
    blockSum ops input row = balanced ops.add (warpSum ops input row) 4 0 :=
  logical16_lane_zero _ _

/-- All source thread-local traversal indices lie in their declared row. -/
theorem thread_cells_bound (tid col : Nat) (ht : tid < 1024) (hc : col ∈ threadCells tid) :
    col < 16384 := by
  obtain ⟨iteration, hi, hj⟩ := List.mem_flatMap.mp hc
  have hi := List.mem_range.mp hi
  obtain ⟨component, hj, he⟩ := List.mem_map.mp (show col ∈ (List.range 8).map
    (fun component => (tid + iteration * 1024) * 8 + component) from by simpa using hj)
  have hj := List.mem_range.mp hj
  omega

#print axioms warp_sum_tree
#print axioms block_sum_tree
#print axioms thread_cells_bound
end LarkNativeRmsNorm
