import Mathlib.Data.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Exact-real value invariant for the normalized online update used by
flash-attention-minimal. This is an algorithm lemma, not a GPU execution,
source-translation, race-freedom or floating-point theorem. A finite first tile
initializes the accumulator; the upstream -infinity sentinel is not a real.
-/
namespace LarkReal.OnlineSoftmax

structure Entry where
  score : ℝ
  value : Nat → ℝ

noncomputable def weight (m : ℝ) (xs : List Entry) : ℝ :=
  (xs.map fun x => Real.exp (x.score - m)).sum

noncomputable def numerator (m : ℝ) (xs : List Entry) (c : Nat) : ℝ :=
  (xs.map fun x => Real.exp (x.score - m) * x.value c).sum

/-- Independent dense softmax-weighted value, with no tile state. -/
noncomputable def reference (xs : List Entry) (c : Nat) : ℝ :=
  numerator 0 xs c / weight 0 xs

structure Accumulator where
  m : ℝ
  l : ℝ
  o : Nat → ℝ

def Valid (xs : List Entry) (a : Accumulator) : Prop :=
  0 < a.l ∧ a.l = weight a.m xs ∧
    ∀ c, a.o c = numerator a.m xs c / a.l

noncomputable def start (m : ℝ) (xs : List Entry) : Accumulator :=
  ⟨m, weight m xs, fun c => numerator m xs c / weight m xs⟩

/-- Source order: m_new=max; l_new=old_scale*l+tile_scale*tile_l;
    O_new=(1/l_new)*(l*old_scale*O+tile_scale*tile_pv). -/
noncomputable def update (a : Accumulator) (tileM : ℝ) (tile : List Entry) : Accumulator :=
  let m := max a.m tileM
  let l := Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile
  ⟨m, l, fun c => (1 / l) *
    ((a.l * Real.exp (a.m - m) * a.o c) +
      (Real.exp (tileM - m) * numerator tileM tile c))⟩

theorem exp_rescale (x a b : ℝ) :
    Real.exp (a - b) * Real.exp (x - a) = Real.exp (x - b) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem weight_shift (xs : List Entry) (a b : ℝ) :
    Real.exp (a - b) * weight a xs = weight b xs := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    simp only [weight, List.map_cons, List.sum_cons] at ih ⊢
    rw [mul_add, exp_rescale, ih]

theorem numerator_shift (xs : List Entry) (a b : ℝ) (c : Nat) :
    Real.exp (a - b) * numerator a xs c = numerator b xs c := by
  induction xs with
  | nil => simp [numerator]
  | cons x xs ih =>
    simp only [numerator, List.map_cons, List.sum_cons] at ih ⊢
    rw [mul_add, ← mul_assoc, exp_rescale, ih]

theorem weight_append (xs ys : List Entry) (m : ℝ) :
    weight m (xs ++ ys) = weight m xs + weight m ys := by
  simp [weight]

theorem numerator_append (xs ys : List Entry) (m : ℝ) (c : Nat) :
    numerator m (xs ++ ys) c = numerator m xs c + numerator m ys c := by
  simp [numerator]

theorem weight_nonneg (xs : List Entry) (m : ℝ) : 0 ≤ weight m xs := by
  induction xs with
  | nil => simp [weight]
  | cons x xs ih =>
    exact add_nonneg (Real.exp_pos _).le ih

theorem weight_pos (xs : List Entry) (m : ℝ) (hne : xs ≠ []) :
    0 < weight m xs := by
  cases xs with
  | nil => contradiction
  | cons x xs => exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (weight_nonneg xs m)

theorem start_valid (xs : List Entry) (m : ℝ) (hne : xs ≠ []) :
    Valid xs (start m xs) := by
  exact ⟨weight_pos xs m hne, rfl, fun _ => rfl⟩

/-- A nonempty processed prefix makes every subsequent denominator positive,
even if an additional tile is empty. No positivity is assumed for values. -/
theorem update_valid (xs tile : List Entry) (a : Accumulator) (tileM : ℝ)
    (ha : Valid xs a) : Valid (xs ++ tile) (update a tileM tile) := by
  obtain ⟨hpos, hl, ho⟩ := ha
  let m := max a.m tileM
  have hlnew : Real.exp (a.m - m) * a.l +
      Real.exp (tileM - m) * weight tileM tile = weight m (xs ++ tile) := by
    rw [hl, weight_shift, weight_shift, weight_append]
  have hnewpos : 0 < weight m (xs ++ tile) := by
    rw [← hlnew]
    exact add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) hpos)
      (mul_nonneg (Real.exp_pos _).le (weight_nonneg tile tileM))
  refine ⟨?_, hlnew, ?_⟩
  · change 0 < Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile
    rw [hlnew]
    exact hnewpos
  · intro c
    change (1 / (Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile)) *
      (a.l * Real.exp (a.m - m) * a.o c +
        Real.exp (tileM - m) * numerator tileM tile c) =
      numerator m (xs ++ tile) c /
        (Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile)
    rw [ho]
    have hold : a.l * Real.exp (a.m - m) * (numerator a.m xs c / a.l) =
        Real.exp (a.m - m) * numerator a.m xs c := by
      field_simp [ne_of_gt hpos]
      ring
    rw [hold, numerator_shift, numerator_shift, ← numerator_append]
    simp only [one_div, div_eq_mul_inv, one_mul]
    exact mul_comm (Real.exp (a.m - m) * a.l + Real.exp (tileM - m) * weight tileM tile)⁻¹
      (numerator m (xs ++ tile) c)

/-- The normalization shift cancels, so the invariant denotes dense attention. -/
theorem valid_reference (xs : List Entry) (a : Accumulator) (ha : Valid xs a) (c : Nat) :
    a.o c = reference xs c := by
  obtain ⟨hpos, hl, ho⟩ := ha
  rw [ho, hl]
  have hn := numerator_shift xs a.m 0 c
  have hw := weight_shift xs a.m 0
  unfold reference
  rw [← hn, ← hw]
  exact (mul_div_mul_left _ _ (Real.exp_pos (a.m - 0)).ne').symm

noncomputable def process (a : Accumulator) (tiles : List (ℝ × List Entry)) : Accumulator :=
  tiles.foldl (fun a tile => update a tile.1 tile.2) a

theorem process_valid (tiles : List (ℝ × List Entry)) (xs : List Entry) (a : Accumulator)
    (ha : Valid xs a) :
    Valid (xs ++ (tiles.map Prod.snd).flatten) (process a tiles) := by
  induction tiles generalizing xs a with
  | nil => simpa [process] using ha
  | cons tile tiles ih =>
    have h := ih (xs ++ tile.2) (update a tile.1 tile.2) (update_valid xs tile.2 a tile.1 ha)
    simpa [process, List.append_assoc] using h

/-- Any finite ordered tiling, arbitrary real scores/values, all value columns.
The first tile must contain an entry; later tiles may have arbitrary lengths. -/
theorem process_reference (first : List Entry) (firstM : ℝ)
    (tiles : List (ℝ × List Entry)) (hne : first ≠ []) (c : Nat) :
    (process (start firstM first) tiles).o c =
      reference (first ++ (tiles.map Prod.snd).flatten) c := by
  exact valid_reference _ _ (process_valid tiles first _ (start_valid first firstM hne)) c

/-- A finite nonempty tile uses its true maximum; the empty case is arbitrary
and is used only for subsequent zero-contribution tiles. -/
noncomputable def peak : List Entry → ℝ
  | [] => 0
  | x :: xs => xs.foldl (fun m x => max m x.score) x.score

noncomputable def run (first : List Entry) (tiles : List (List Entry)) : Accumulator :=
  process (start (peak first) first) (tiles.map fun tile => (peak tile, tile))

theorem run_reference (first : List Entry) (tiles : List (List Entry))
    (hne : first ≠ []) (c : Nat) :
    (run first tiles).o c = reference (first ++ tiles.flatten) c := by
  simpa [run, List.map_map, Function.comp_def] using
    process_reference first (peak first) (tiles.map fun tile => (peak tile, tile)) hne c

#print axioms exp_rescale
#print axioms weight_shift
#print axioms numerator_shift
#print axioms weight_pos
#print axioms update_valid
#print axioms valid_reference
#print axioms process_valid
#print axioms process_reference
#print axioms run_reference
end LarkReal.OnlineSoftmax
