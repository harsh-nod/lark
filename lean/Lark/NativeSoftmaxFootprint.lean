import Lark.NativeSoftmaxAddress

/-! Sufficient source-phase access obligations for the guarded repair.
This theorem does not assume race freedom. A whole-source proof must still
derive classification for every access of its actual trace.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

inductive Good (a : Access) : Prop
  | input (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 1) (read : a.write = false)
  | output (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = 0) (thread : a.thread = writer a.location.offset)
  | privateAccess (space : a.location.space = .local) (owner : a.location.owner = a.thread)
  | partialStore (space : a.location.space = .shared) (owner : a.location.owner = a.thread / 1024)
      (bank : a.location.buffer < 2) (offset : a.location.offset = (a.thread % 1024) / 32)
      (lane : (a.thread % 1024) % 32 = 0) (phase : a.epoch.block = 2 * a.location.buffer)
      (write : a.write = true)
  | serialAccess (space : a.location.space = .shared) (owner : a.location.owner = a.thread / 1024)
      (bank : a.location.buffer < 2) (thread : a.thread % 1024 = 0)
      (phase : a.epoch.block = 2 * a.location.buffer + 1)
  | broadcastRead (space : a.location.space = .shared) (owner : a.location.owner = a.thread / 1024)
      (bank : a.location.buffer < 2) (offset : a.location.offset = 0)
      (phase : a.epoch.block = 2 * a.location.buffer + 2) (read : a.write = false)

theorem ordered_blocks (p : Shape) (a b : Access)
    (block : a.thread / 1024 = b.thread / 1024)
    (epochs : a.epoch.block ≠ b.epoch.block) : ordered (geometry p) a b = true := by
  simp [ordered,geometry,block,epochs]

theorem collision (p : Shape) (a b : Access) (ha : Good a) (hb : Good b)
    (same : a.location = b.location) :
    a.thread = b.thread ∨ (a.write = false ∧ b.write = false) ∨ ordered (geometry p) a b = true := by
  have hs := congrArg Location.space same
  have ho := congrArg Location.owner same
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all
  all_goals try omega
  all_goals
    first
    | (right; apply ordered_blocks p a b <;> omega)
    | (right; right; apply ordered_blocks p a b <;> omega)
    | (apply ordered_blocks p a b <;> omega)

theorem sameLocation_true_iff (a b : Location) : sameLocation a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameLocation,Bool.and_eq_true,Location.mk.injEq,and_assoc]

theorem conflict_false (p : Shape) (a b : Access) (ha : Good a) (hb : Good b) :
    conflict (geometry p) a b = false := by
  by_cases hs : a.location = b.location
  · rcases collision p a b ha hb hs with ht | hr | ho
    · simp [conflict,ht]
    · simp [conflict,hr.1,hr.2]
    · simp [conflict,ho]
  · have hl : sameLocation a.location b.location = false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (hs ((sameLocation_true_iff _ _).mp h))
    simp [conflict,hl]

theorem race_free (p : Shape) (trace : List Access)
    (good : ∀ a ∈ trace, Good a) : raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p a b (good a ha) (good b hb)]

#print axioms ordered_blocks
#print axioms collision
#print axioms conflict_false
#print axioms race_free
end LarkNativeSoftmax
