import Lark.NativeAttentionProgram

/-! Sufficient per-access obligations for native tiled attention. A whole-launch
proof still has to derive them for every actual access of the pinned program. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def writer (offset : Nat) : Nat := offset / 32768 * 32 + offset / 256 % 32
def privateWidth (buffer : Nat) : Nat := if buffer = 0 then 256 else 32

inductive Good (a : Access) : Prop
  | input (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer ≠ 0) (read : a.write = false)
  | output (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 0) (thread : a.thread = writer a.location.offset)
  | localAccess (space : a.location.space = .local) (owner : a.location.owner = a.thread)
  | privateShared (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 32)
      (buffer : a.location.buffer = 0 ∨ a.location.buffer = 3)
      (thread : a.thread % 32 = a.location.offset / privateWidth a.location.buffer)
  | tileStore (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 32)
      (buffer : a.location.buffer = 1 ∨ a.location.buffer = 2)
      (thread : a.thread % 32 = a.location.offset / 256)
      (phase : a.epoch.block % 2 = 0) (write : a.write = true)
  | tileLoad (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / 32)
      (buffer : a.location.buffer = 1 ∨ a.location.buffer = 2)
      (phase : a.epoch.block % 2 = 1) (read : a.write = false)

theorem thread_eq_of_owner_lane (a b : Nat) (owner : a / 32 = b / 32)
    (lane : a % 32 = b % 32) : a = b := by omega

theorem ordered_blocks (p : Shape) (a b : Access)
    (block : a.thread / 32 = b.thread / 32)
    (epochs : a.epoch.block ≠ b.epoch.block) : ordered (geometry p) a b = true := by
  simp [ordered, geometry, block, epochs]

theorem collision (p : Shape) (a b : Access) (ha : Good a) (hb : Good b)
    (same : a.location = b.location) :
    a.thread = b.thread ∨ (a.write = false ∧ b.write = false) ∨ ordered (geometry p) a b = true := by
  have hs := congrArg Location.space same
  have ho := congrArg Location.owner same
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all
  all_goals try omega
  case tileStore.tileLoad =>
    right
    apply ordered_blocks p a b <;> omega
  case tileLoad.tileStore =>
    right
    apply ordered_blocks p a b <;> omega

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

/-- The actual machine's quadratic RF check follows from local obligations.
No race-freedom premise is assumed; access classification remains to be proved. -/
theorem race_free (p : Shape) (trace : List Access)
    (good : ∀ a ∈ trace, Good a) : raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p a b (good a ha) (good b hb)]

/-- Private array slots are owned by the actual thread, not by its block. -/
theorem location_local (l : Layout) (g : Geometry) (t b i size : Nat) (write : Bool)
    (hs : l.locals[b]? = some size) (hi : i < size) :
    location l g t .local b (i : Int) write = some ⟨.local, t, b, i⟩ := by
  simp [location, hs, hi]

#print axioms collision
#print axioms race_free
#print axioms location_local
end LarkNativeAttention
