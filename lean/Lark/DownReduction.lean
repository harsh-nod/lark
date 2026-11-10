import Lark.Collective

/-! The guarded ascending shuffle-down reduction used by native RMSNorm.
These value lemmas describe a component recurrence, not a whole launch.
-/
namespace LarkDownReduction
open LarkNonlinear

/-- Contiguous balanced tree; no associativity law is assumed for `add`. -/
def balanced (add : α → α → α) (values : Nat → α) : Nat → Nat → α
  | 0, lane => values lane
  | n + 1, lane => add (balanced add values n lane)
      (balanced add values n (lane + 2 ^ n))

/-- Guarded source recurrence, including the native out-of-range self source. -/
def reduced (add : α → α → α) (width valid : Nat) (values : Nat → α) : Nat → Nat → α
  | 0, lane => values lane
  | n + 1, lane =>
      if lane + 2 ^ n < valid then
        add (reduced add width valid values n lane)
          (reduced add width valid values n (if lane + 2 ^ n < width then lane + 2 ^ n else lane))
      else reduced add width valid values n lane

theorem source_down (width lane distance : Nat) (hw : 0 < width) (hl : lane < width)
    (hd : distance < width) (hb : width ≤ 64)
    (supported : [1, 2, 4, 8, 16, 32, 64].contains width = true) :
    LarkCollective.sourceLane .down width lane distance =
      some (if lane + distance < width then lane + distance else lane) := by
  have h64 : lane < 64 := by omega
  have hle : distance ≤ width := by omega
  unfold LarkCollective.sourceLane
  rewrite [supported]
  by_cases hs : lane + distance < width
  · have hs64 : lane + distance < 64 := by omega
    simp [h64, hle, Nat.mod_eq_of_lt hl,
      Nat.div_eq_of_lt hl, hs, hs64, Nat.div_eq_of_lt hs]
  · simp [h64, hle, Nat.mod_eq_of_lt hl,
      Nat.div_eq_of_lt hl, hs]

/-- Only complete subtrees are used by lane zero; overflowing peers do not matter. -/
theorem complete_subtree (add : α → α → α) (values : Nat → α)
    (width valid n lane : Nat) (hv : width ≤ valid) (h : lane + 2 ^ n ≤ width) :
    reduced add width valid values n lane = balanced add values n lane := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih =>
      have hp : 0 < 2 ^ n := Nat.two_pow_pos n
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      have ha : lane + 2 ^ n < width := by rewrite [hpow] at h; omega
      have hb : lane + 2 ^ n < valid := by omega
      have hl : lane + 2 ^ n ≤ width := by omega
      have hr : (lane + 2 ^ n) + 2 ^ n ≤ width := by rewrite [hpow] at h; omega
      simp only [reduced, hb, ha, ↓reduceIte, balanced]
      rewrite [ih lane hl, ih (lane + 2 ^ n) hr]
      rfl

theorem wave64_lane_zero (add : α → α → α) (values : Nat → α) (valid : Nat)
    (hv : 64 ≤ valid) :
    reduced add 64 valid values 6 0 = balanced add values 6 0 :=
  complete_subtree add values 64 valid 6 0 hv (by decide)

theorem logical16_lane_zero (add : α → α → α) (values : Nat → α) :
    reduced add 16 16 values 4 0 = balanced add values 4 0 :=
  complete_subtree add values 16 16 4 0 (by decide) (by decide)

def leaves : Nat → Nat → List Nat
  | 0, lane => [lane]
  | n + 1, lane => leaves n lane ++ leaves n (lane + 2 ^ n)

/-- The chosen reduction contains every contiguous lane exactly once, in order. -/
theorem leaves_range (n lane : Nat) : leaves n lane = List.range' lane (2 ^ n) := by
  induction n generalizing lane with
  | zero => simp [leaves]
  | succ n ih =>
      rewrite [leaves, ih, ih]
      have h := List.range'_append (s := lane) (m := 2 ^ n) (n := 2 ^ n) (step := 1)
      simpa only [Nat.one_mul, Nat.pow_succ, Nat.mul_two] using h

#print axioms source_down
#print axioms complete_subtree
#print axioms leaves_range
end LarkDownReduction
