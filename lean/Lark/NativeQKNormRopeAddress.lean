import Lark.NativeQKNormRopeProgram

/-! Native head/lane ownership and bounds. The footprint theorem is conditional;
classification of the complete source trace remains an execution obligation. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def row (t : Nat) := t / 1280
def head (t : Nat) := (t / 32) % 40
def column (t e : Nat) := t % 32 * 4 + e
def outputAddress (t e : Nat) := row t * 5120 + head t * 128 + column t e
def inputAddress (t e : Nat) := row t * 6144 + head t * 128 + column t e

theorem native_head (t : Nat) : t / 256 * 8 + t % 256 / 32 = t / 32 := by omega
theorem native_row (t : Nat) : (t / 32) / 40 = row t := by simp [row, Nat.div_div_eq_div_mul]
theorem thread_decomposition (t : Nat) : t = row t * 1280 + head t * 32 + t % 32 := by
  simp only [row, head]
  omega
theorem head_bound (t : Nat) : head t < 40 := Nat.mod_lt _ (by decide)
theorem column_bound (t e : Nat) (he : e < 4) : column t e < 128 := by
  have := Nat.mod_lt t (by decide : 0 < 32)
  simp only [column]
  omega
theorem output_linear (t e : Nat) : outputAddress t e = t * 4 + e := by
  have h := thread_decomposition t
  simp only [outputAddress, column]
  omega
theorem output_owner (t e : Nat) (he : e < 4) : outputAddress t e / 4 = t := by
  rw [output_linear]
  omega
theorem row_bound (p : Shape) (t : Nat) (ht : t < p.rows * 1280) : row t < p.rows := by
  simp only [row]
  omega
theorem output_bound (p : Shape) (t e : Nat) (ht : t < p.rows * 1280) (he : e < 4) :
    outputAddress t e < p.rows * 5120 := by
  rw [output_linear]
  omega
theorem input_bound (p : Shape) (t e : Nat) (ht : t < p.rows * 1280) (he : e < 4) :
    inputAddress t e < p.rows * 6144 := by
  have hr := row_bound p t ht
  have hh := head_bound t
  have hc := column_bound t e he
  simp only [inputAddress]
  omega
theorem input_never_v (t e : Nat) (he : e < 4) :
    row t * 6144 ≤ inputAddress t e ∧ inputAddress t e < row t * 6144 + 5120 := by
  have hh := head_bound t
  have hc := column_bound t e he
  simp only [inputAddress]
  omega
theorem output_coverage (p : Shape) (i : Nat) (hi : i < p.rows * 5120) :
    ∃ t < p.rows * 1280, ∃ e < 4, outputAddress t e = i := by
  refine ⟨i / 4, by omega, i % 4, Nat.mod_lt _ (by decide), ?_⟩
  rw [output_linear]
  omega
theorem signed_bounds (p : Shape) (t e : Nat) (ht : t < p.rows * 1280) (he : e < 4) :
    inputAddress t e < 2147483648 ∧ outputAddress t e < 2147483648 := by
  have hi := input_bound p t e ht he
  have ho := output_bound p t e ht he
  have hb := p.bound
  omega

inductive Good (a : Access) : Prop
  | input (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : 1 ≤ a.location.buffer ∧ a.location.buffer ≤ 4) (read : a.write = false)
  | output (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 0) (thread : a.thread = a.location.offset / 4)

theorem collision (a b : Access) (ha : Good a) (hb : Good b) (same : a.location = b.location) :
    a.thread = b.thread ∨ (a.write = false ∧ b.write = false) := by
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all <;> omega

theorem sameLocation_true_iff (a b : Location) : sameLocation a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameLocation, Bool.and_eq_true, Location.mk.injEq, and_assoc]

theorem conflict_false (p : Shape) (a b : Access) (ha : Good a) (hb : Good b) :
    conflict (geometry p) a b = false := by
  by_cases hs : a.location = b.location
  · rcases collision a b ha hb hs with ht | hr
    · simp [conflict, ht]
    · simp [conflict, hr.1, hr.2]
  · have hl : sameLocation a.location b.location = false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (hs ((sameLocation_true_iff _ _).mp h))
    simp [conflict, hl]

theorem race_free (p : Shape) (trace : List Access) (good : ∀ a ∈ trace, Good a) :
    raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p a b (good a ha) (good b hb)]

#print axioms native_head
#print axioms native_row
#print axioms thread_decomposition
#print axioms head_bound
#print axioms column_bound
#print axioms output_linear
#print axioms output_owner
#print axioms row_bound
#print axioms output_bound
#print axioms input_bound
#print axioms input_never_v
#print axioms output_coverage
#print axioms signed_bounds
#print axioms collision
#print axioms sameLocation_true_iff
#print axioms conflict_false
#print axioms race_free
end LarkNativeQKNormRope
