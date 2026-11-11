import Lark.NativeRopeCoordinates
import Lark.NativeRopeRound

/-! Independently column-indexed dense rotary reference, matching the two
closed PyTorch layouts. Equality retains all explicit half conversions and
source multiplication/add/subtraction order under arbitrary scalar operators. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def denseJ (neox : Bool) (col : Nat) : Nat := if neox then col % 64 else col % 128 / 2
def denseX (neox : Bool) (col : Nat) : Nat :=
  col / 128 * 128 + if neox then denseJ neox col else 2 * denseJ neox col
def denseY (neox : Bool) (col : Nat) : Nat :=
  col / 128 * 128 + if neox then denseJ neox col + 64 else 2 * denseJ neox col + 1
def denseImaginary (neox : Bool) (col : Nat) : Bool :=
  if neox then decide (64 ≤ col % 128) else decide (col % 2 = 1)

def denseResult (ops : Ops α) (input : Nat → Nat → α) (buffer row col : Nat) (neox : Bool) : α :=
  let x := ops.fromHalf (input buffer (row * width buffer + denseX neox col))
  let y := ops.fromHalf (input buffer (row * width buffer + denseY neox col))
  let c := ops.fromHalf (input 2 (row * 128 + denseJ neox col))
  let sn := ops.fromHalf (input 2 (row * 128 + denseJ neox col + 64))
  ops.toHalf (if denseImaginary neox col then ops.add (ops.mul y c) (ops.mul x sn)
    else ops.sub (ops.mul x c) (ops.mul y sn))

theorem dense_j_of_pair (neox imaginary : Bool) (pair : Nat) :
    denseJ neox (pairColumn neox pair imaginary) = pair % 64 := by
  cases neox <;> cases imaginary <;> simp [denseJ, pairColumn] <;> omega

theorem dense_x_of_pair (neox imaginary : Bool) (pair : Nat) :
    denseX neox (pairColumn neox pair imaginary) = pairColumn neox pair false := by
  rw [denseX, dense_j_of_pair]
  cases neox <;> cases imaginary <;> simp [pairColumn] <;> omega

theorem dense_y_of_pair (neox imaginary : Bool) (pair : Nat) :
    denseY neox (pairColumn neox pair imaginary) = pairColumn neox pair true := by
  rw [denseY, dense_j_of_pair]
  cases neox <;> cases imaginary <;> simp [pairColumn] <;> omega

theorem dense_imaginary_of_pair (neox imaginary : Bool) (pair : Nat) :
    denseImaginary neox (pairColumn neox pair imaginary) = imaginary := by
  cases neox <;> cases imaginary <;> simp [denseImaginary, pairColumn] <;> omega

theorem dense_at_pair (ops : Ops α) (input : Nat → Nat → α) (buffer row pair : Nat) (neox imaginary : Bool) :
    denseResult ops input buffer row (pairColumn neox pair imaginary) neox =
      rotated ops input buffer row pair neox imaginary := by
  simp only [denseResult, rotated, dense_x_of_pair, dense_y_of_pair,
    dense_j_of_pair, dense_imaginary_of_pair, address, cacheCos, cacheSin, pairReal, pairImaginary]

#print axioms dense_j_of_pair
#print axioms dense_x_of_pair
#print axioms dense_y_of_pair
#print axioms dense_imaginary_of_pair
#print axioms dense_at_pair
end LarkNativeRope
