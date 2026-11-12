import LarkReal.NativeQKNormRopeTree

/-! The native reduction equals an independently indexed dense 128-element
head sum over exact reals. No register or instruction state occurs in headSum. -/
namespace LarkReal.NativeQKNormRope
open LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def headSquare (input : Nat → Nat → ℝ) (r h c : Nat) : ℝ :=
  input 1 (r * 6144 + h * 128 + c) * input 1 (r * 6144 + h * 128 + c)
def headSum (input : Nat → Nat → ℝ) (r h : Nat) : ℝ :=
  ((List.range 128).map (headSquare input r h)).sum

theorem square_prefix_sum (input : Nat → Nat → ℝ) (t n : Nat) :
    squarePrefix ops input t n = ((List.range n).map (fun e => headSquare input (row t) (head t) (column t e))).sum := by
  induction n with
  | zero => simp [squarePrefix, ops]
  | succ n ih =>
      rw [squarePrefix, List.range_succ, List.map_append, List.sum_append]
      change squarePrefix ops input t n + headSquare input (row t) (head t) (column t n) = _
      rw [ih]
      simp

theorem peer_coords (block warp lane j : Nat) (hj : j < 32) :
    let t := cohortBase block warp + lane
    let peer := cohortBase block warp + (lane / 32 * 32 + j)
    row peer = row t ∧ head peer = head t ∧ peer % 32 = j := by
  dsimp only
  unfold row head cohortBase
  omega

theorem peer_square_sum (input : Nat → Nat → ℝ) (block warp lane j : Nat) (hj : j < 32) :
    let t := cohortBase block warp + lane
    squarePrefix ops input (cohortBase block warp + (lane / 32 * 32 + j)) 4 =
      ((List.range' (j * 4) 4).map (headSquare input (row t) (head t))).sum := by
  have coords := peer_coords block warp lane j hj
  dsimp only at coords ⊢
  rw [square_prefix_sum]
  simp only [coords.1, coords.2.1, column, coords.2.2, List.range'_eq_map_range,
    List.map_map, Function.comp_def, Nat.one_mul]

theorem sum_blocks (values : Nat → ℝ) (n width start : Nat) :
    ((List.range n).map (fun block =>
      ((List.range' (start + block * width) width).map values).sum)).sum =
      ((List.range' start (n * width)).map values).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      rw [← List.sum_append, ← List.map_append]
      have he := List.range'_append (s := start) (m := n * width) (n := width) (step := 1)
      simpa only [Nat.one_mul, Nat.add_mul, Nat.one_mul] using
        congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem wave_sum_eq_dense (input : Nat → Nat → ℝ) (block warp lane : Nat) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    waveValues ops input block warp 5 lane = headSum input (row t) (head t) := by
  dsimp only
  rw [wave_sum input block warp lane hl]
  have parts :
      ((List.range' (lane / 32 * 32) 32).map (fun l => squarePrefix ops input (cohortBase block warp + l) 4)).sum =
      ((List.range 32).map (fun j => ((List.range' (j * 4) 4).map
        (headSquare input (row (cohortBase block warp + lane)) (head (cohortBase block warp + lane)))).sum)).sum := by
    simp only [List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.one_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    simpa only [List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.one_mul] using
      peer_square_sum input block warp lane j (List.mem_range.mp hj)
  rw [parts]
  unfold headSum
  simpa only [Nat.zero_add, ← List.range_eq_range'] using
    sum_blocks (headSquare input (row (cohortBase block warp + lane)) (head (cohortBase block warp + lane))) 32 4 0

#print axioms square_prefix_sum
#print axioms peer_coords
#print axioms peer_square_sum
#print axioms sum_blocks
#print axioms wave_sum_eq_dense
end LarkReal.NativeQKNormRope
