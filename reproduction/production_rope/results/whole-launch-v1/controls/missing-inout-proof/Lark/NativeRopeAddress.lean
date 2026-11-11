import Lark.NativeRopeProgram

/-! Pair coverage and ownership for both native layouts. Actual execution must
separately establish the conditional footprint for its entire trace. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def pairColumn (neox : Bool) (pair : Nat) (imaginary : Bool) : Nat :=
  pair / 64 * 128 +
    if neox then pair % 64 + (if imaginary then 64 else 0)
    else pair % 64 * 2 + (if imaginary then 1 else 0)

def pairOfColumn (neox : Bool) (col : Nat) : Nat :=
  col / 128 * 64 + if neox then col % 64 else col % 128 / 2

def width (buffer : Nat) : Nat := if buffer = 0 then 4096 else 1024
def pairs (buffer : Nat) : Nat := if buffer = 0 then 2048 else 512
def address (buffer row pair : Nat) (neox imaginary : Bool) : Nat :=
  row * width buffer + pairColumn neox pair imaginary
def writer (buffer offset : Nat) (neox : Bool) : Nat :=
  offset / width buffer * 512 + pairOfColumn neox (offset % width buffer) % 512

theorem pair_column_bound (neox imaginary : Bool) (heads pair : Nat)
    (hp : pair < heads * 64) : pairColumn neox pair imaginary < heads * 128 := by
  cases neox <;> cases imaginary <;> simp only [pairColumn, Bool.false_eq_true, if_false, if_true]
  all_goals omega

theorem pair_inverse (neox imaginary : Bool) (pair : Nat) :
    pairOfColumn neox (pairColumn neox pair imaginary) = pair := by
  cases neox <;> cases imaginary <;>
    simp only [pairOfColumn, pairColumn, Bool.false_eq_true, if_false, if_true]
  all_goals omega

theorem pair_columns_distinct (neox : Bool) (pair : Nat) :
    pairColumn neox pair false ≠ pairColumn neox pair true := by
  cases neox <;> simp [pairColumn] <;> omega

theorem column_coverage (neox : Bool) (heads col : Nat) (hc : col < heads * 128) :
    ∃ pair < heads * 64, ∃ imaginary : Bool, pairColumn neox pair imaginary = col := by
  cases neox
  · refine ⟨pairOfColumn false col, ?_, decide (col % 2 = 1), ?_⟩
    · simp only [pairOfColumn, Bool.false_eq_true, if_false]; omega
    · by_cases h : col % 2 = 1 <;> simp [pairColumn, pairOfColumn, h] <;> omega
  · refine ⟨pairOfColumn true col, ?_, decide (64 ≤ col % 128), ?_⟩
    · simp only [pairOfColumn, if_true]; omega
    · by_cases h : 64 ≤ col % 128 <;> simp [pairColumn, pairOfColumn, h] <;> omega

theorem column_bound (buffer pair : Nat) (neox imaginary : Bool)
    (hp : pair < pairs buffer) : pairColumn neox pair imaginary < width buffer := by
  by_cases h : buffer = 0
  · simpa [width, h] using pair_column_bound neox imaginary 32 pair (by simpa [pairs, h] using hp)
  · simpa [width, h] using pair_column_bound neox imaginary 8 pair (by simpa [pairs, h] using hp)

theorem address_bound (p : Shape) (buffer row pair : Nat) (neox imaginary : Bool)
    (hr : row < p.rows) (hp : pair < pairs buffer) :
    address buffer row pair neox imaginary < p.rows * width buffer := by
  have hc := column_bound buffer pair neox imaginary hp
  unfold address
  by_cases h : buffer = 0 <;> simp [width, h] at * <;> omega

theorem address_int32 (p : Shape) (buffer row pair : Nat) (neox imaginary : Bool)
    (hr : row < p.rows) (hp : pair < pairs buffer) :
    address buffer row pair neox imaginary < 2147483648 := by
  have hb := address_bound p buffer row pair neox imaginary hr hp
  have hs := p.bound
  by_cases h : buffer = 0 <;> simp [width, h] at * <;> omega

theorem address_writer (buffer row pair : Nat) (neox imaginary : Bool)
    (hp : pair < pairs buffer) :
    writer buffer (address buffer row pair neox imaginary) neox = row * 512 + pair % 512 := by
  have hc := column_bound buffer pair neox imaginary hp
  have hw : 0 < width buffer := by unfold width; split <;> decide
  have hd : address buffer row pair neox imaginary / width buffer = row := by
    by_cases h : buffer = 0 <;> simp [address, width, h] at * <;> omega
  have hm : address buffer row pair neox imaginary % width buffer = pairColumn neox pair imaginary := by
    by_cases h : buffer = 0 <;> simp [address, width, h] at * <;> omega
  simp only [writer, hd, hm, pair_inverse]

theorem native_pair_bound (buffer tid iteration : Nat)
    (ht : tid < 512) (hi : iteration < (if buffer = 0 then 4 else 1)) :
    tid + iteration * 512 < pairs buffer := by
  unfold pairs
  split <;> split at hi <;> omega

theorem native_writer (buffer row tid iteration : Nat) (neox imaginary : Bool)
    (ht : tid < 512) (hi : iteration < (if buffer = 0 then 4 else 1)) :
    writer buffer (address buffer row (tid + iteration * 512) neox imaginary) neox =
      row * 512 + tid := by
  rw [address_writer buffer row _ neox imaginary (native_pair_bound buffer tid iteration ht hi)]
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

inductive Good (neox : Bool) (a : Access) : Prop
  | cache (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 2) (read : a.write = false)
  | mutableGlobal (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 0 ∨ a.location.buffer = 1)
      (thread : a.thread = writer a.location.buffer a.location.offset neox)

theorem collision (neox : Bool) (a b : Access) (ha : Good neox a) (hb : Good neox b)
    (same : a.location = b.location) : a.thread = b.thread ∨ (a.write = false ∧ b.write = false) := by
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all

theorem sameLocation_true_iff (a b : Location) : sameLocation a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameLocation, Bool.and_eq_true, Location.mk.injEq, and_assoc]

theorem conflict_false (p : Shape) (neox : Bool) (a b : Access)
    (ha : Good neox a) (hb : Good neox b) : conflict (geometry p) a b = false := by
  by_cases hs : a.location = b.location
  · rcases collision neox a b ha hb hs with ht | hr
    · simp [conflict, ht]
    · simp [conflict, hr.1, hr.2]
  · have hl : sameLocation a.location b.location = false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (hs ((sameLocation_true_iff _ _).mp h))
    simp [conflict, hl]

theorem race_free (p : Shape) (neox : Bool) (trace : List Access)
    (good : ∀ a ∈ trace, Good neox a) : raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p neox a b (good a ha) (good b hb)]

#print axioms pair_column_bound
#print axioms pair_inverse
#print axioms pair_columns_distinct
#print axioms column_coverage
#print axioms column_bound
#print axioms address_bound
#print axioms address_int32
#print axioms address_writer
#print axioms native_pair_bound
#print axioms native_writer
#print axioms collision
#print axioms sameLocation_true_iff
#print axioms conflict_false
#print axioms race_free
end LarkNativeRope
