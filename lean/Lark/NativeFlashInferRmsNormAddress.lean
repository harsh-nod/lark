import Lark.NativeFlashInferRmsNormProgram

/-! Native address ownership and a conditional footprint theorem.
The actual source execution must still be shown to satisfy `Good`. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def column (tid iteration component : Nat) : Nat := (iteration * 1024 + tid) * 8 + component
def address (row col : Nat) : Nat := row * 16384 + col
def writer (offset : Nat) : Nat := offset / 16384 * 1024 + (offset % 16384 / 8) % 1024

theorem column_bound (tid iteration component : Nat)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    column tid iteration component < 16384 := by
  unfold column
  omega

theorem address_bound (p : Shape) (row tid iteration component : Nat)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    address row (column tid iteration component) < p.rows * 16384 := by
  have h := column_bound tid iteration component ht hi hc
  unfold address
  omega

theorem address_int32 (p : Shape) (row tid iteration component : Nat)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    address row (column tid iteration component) < 2147483648 := by
  have h := address_bound p row tid iteration component hr ht hi hc
  have hb := p.bound
  omega

theorem address_writer (row tid iteration component : Nat)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) :
    writer (address row (column tid iteration component)) = row * 1024 + tid := by
  unfold writer address column
  omega

theorem coverage (col : Nat) (hc : col < 16384) :
    ∃ tid < 1024, ∃ iteration < 2, ∃ component < 8, column tid iteration component = col := by
  refine ⟨col / 8 % 1024, by omega, col / 8192, by omega, col % 8, by omega, ?_⟩
  unfold column
  omega

inductive Good (a : Access) : Prop
  | input (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 1 ∨ a.location.buffer = 2) (read : a.write = false)
  | output (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 0) (thread : a.thread = writer a.location.offset)
  | partialStore (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 1024) (buffer : a.location.buffer = 0)
      (thread : a.thread % 1024 = a.location.offset * 32)
      (phase : a.epoch.block = 0) (write : a.write = true)
  | partialRead (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 1024) (buffer : a.location.buffer = 0)
      (thread : a.thread % 1024 = a.location.offset)
      (phase : a.epoch.block = 1) (read : a.write = false)
  | blockStore (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 1024) (buffer : a.location.buffer = 0)
      (offset : a.location.offset = 0) (thread : a.thread % 1024 = 0)
      (phase : a.epoch.block = 1) (write : a.write = true)
  | broadcast (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 1024) (buffer : a.location.buffer = 0)
      (offset : a.location.offset = 0) (phase : a.epoch.block = 2) (read : a.write = false)

theorem ordered_blocks (p : Shape) (a b : Access)
    (same : a.thread / 1024 = b.thread / 1024) (epochs : a.epoch.block ≠ b.epoch.block) :
    ordered (geometry p) a b = true := by simp [ordered, geometry, same, epochs]

theorem collision (p : Shape) (a b : Access) (ha : Good a) (hb : Good b)
    (same : a.location = b.location) :
    a.thread = b.thread ∨ (a.write = false ∧ b.write = false) ∨ ordered (geometry p) a b = true := by
  have hs := congrArg Location.space same
  have ho := congrArg Location.owner same
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all
  all_goals first
    | omega
    | (right; apply ordered_blocks p a b <;> omega)
    | (apply ordered_blocks p a b <;> omega)

theorem sameLocation_true_iff (a b : Location) : sameLocation a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameLocation, Bool.and_eq_true, Location.mk.injEq, and_assoc]

theorem conflict_false (p : Shape) (a b : Access) (ha : Good a) (hb : Good b) :
    conflict (geometry p) a b = false := by
  by_cases hs : a.location = b.location
  · rcases collision p a b ha hb hs with ht | hr | ho
    · simp [conflict, ht]
    · simp [conflict, hr.1, hr.2]
    · simp [conflict, ho]
  · have hl : sameLocation a.location b.location = false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (hs ((sameLocation_true_iff _ _).mp h))
    simp [conflict, hl]

/-- Conditional only; no actual-launch classification premise is discharged. -/
theorem race_free (p : Shape) (trace : List Access)
    (good : ∀ a ∈ trace, Good a) : raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p a b (good a ha) (good b hb)]

#print axioms column_bound
#print axioms address_bound
#print axioms address_int32
#print axioms address_writer
#print axioms coverage
#print axioms ordered_blocks
#print axioms collision
#print axioms sameLocation_true_iff
#print axioms conflict_false
#print axioms race_free
end LarkNativeFlashInferRmsNorm
