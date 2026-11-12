import LarkReal.NativeQKNormRopeReduction
import Lark.NativeQKNormRopeInterleavedResult

/-! Independent dense RMS normalization and interleaved rotary formulas over
exact reals. These formulas contain no machine state or reduction-tree indices. -/
namespace LarkReal.NativeQKNormRope
open LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def denseScale (input : Nat → Nat → ℝ) (r h : Nat) : ℝ :=
  1 / Real.sqrt (headSum input r h / 128 + 1 / 100000)

noncomputable def denseNormalized (input : Nat → Nat → ℝ) (r h c : Nat) : ℝ :=
  input 1 (r * 6144 + h * 128 + c) * (denseScale input r h * input (if h < 32 then 2 else 3) c)

noncomputable def denseInterleaved (input : Nat → Nat → ℝ) (r h c : Nat) : ℝ :=
  let pair := c / 2
  let x := denseNormalized input r h (pair * 2)
  let y := denseNormalized input r h (pair * 2 + 1)
  let cosine := input 4 (r * 128 + pair)
  let sine := input 4 (r * 128 + pair + 64)
  if c % 2 = 0 then x * cosine - y * sine else x * sine + y * cosine

theorem native_sum (input : Nat → Nat → ℝ) (t : Nat) :
    waveValues ops input (physicalBlock t) (physicalWarp t) 5 (physicalLane t) = headSum input (row t) (head t) := by
  simpa only [physical_reconstruct] using
    wave_sum_eq_dense input (physicalBlock t) (physicalWarp t) (physicalLane t) (physical_lane_bound t)

theorem normalized_eq_dense (input : Nat → Nat → ℝ) (t e : Nat) :
    normalizedValue ops input t (weightBuffer t)
      (normalScale ops (waveValues ops input (physicalBlock t) (physicalWarp t) 5 (physicalLane t))) e =
      denseNormalized input (row t) (head t) (column t e) := by
  rw [native_sum]
  simp [normalizedValue, inputValue, weightValue, normalScale, ops, denseNormalized,
    denseScale, inputAddress, weightBuffer]

theorem result_eq_dense (input : Nat → Nat → ℝ) (t e : Nat) :
    interleavedSourceResult ops input t e = denseInterleaved input (row t) (head t) (column t e) := by
  have normals : (fun r => normalizedValue ops input t (weightBuffer t)
      (normalScale ops (waveValues ops input (physicalBlock t) (physicalWarp t) 5 (physicalLane t))) r) =
      (fun r => denseNormalized input (row t) (head t) (column t r)) := by
    funext r
    exact normalized_eq_dense input t r
  unfold interleavedSourceResult
  rw [normals]
  change interleavedOutput ops input (fun r => denseNormalized input (row t) (head t) (column t r)) t e = _
  have pair : column t e / 2 = t % 32 * 2 + e / 2 := by unfold column; omega
  have parity : column t e % 2 = e % 2 := by unfold column; omega
  have realCol : column t (2 * (e / 2)) = column t e / 2 * 2 := by unfold column; omega
  have imaginaryCol : column t (2 * (e / 2) + 1) = column t e / 2 * 2 + 1 := by unfold column; omega
  simp [interleavedOutput, interleavedReal, interleavedImaginary, pairCosValue, pairSinValue,
    pairCosAddress, pairSinAddress, denseInterleaved, pair, parity, realCol, imaginaryCol, ops, Nat.add_assoc]

theorem flat_coords (i : Nat) :
    row (i / 4) = i / 5120 ∧ head (i / 4) = i % 5120 / 128 ∧ column (i / 4) (i % 4) = i % 128 := by
  unfold row head column
  omega

#print axioms native_sum
#print axioms normalized_eq_dense
#print axioms result_eq_dense
#print axioms flat_coords
end LarkReal.NativeQKNormRope
