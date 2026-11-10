import Lark.VectorStride

/-!
Race-freedom obligations for a vector-strided block reduction with shared
warp partials and a later scale broadcast. A complete kernel must still prove
that every actual access belongs to this classification.
-/
namespace LarkReductionFootprint
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def geometry (p : LarkVectorStride.Shape) : Geometry := ⟨p.rows, p.block, 64⟩

inductive Good (p : LarkVectorStride.Shape) (outBuffer : Nat) (a : Access) : Prop
  | input (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer ≠ outBuffer) (read : a.write = false)
  | output (space : a.location.space = .global) (owner : a.location.owner = 0)
      (buffer : a.location.buffer = outBuffer) (write : a.write = true)
      (thread : a.thread = LarkVectorStride.writer p a.location.offset)
  | partialStore (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / p.block) (buffer : a.location.buffer = 0)
      (offset : a.location.offset = (a.thread % p.block) / 64)
      (lane : (a.thread % p.block) % 64 = 0)
      (epoch : a.epoch.block = 0) (write : a.write = true)
  | partialLoad (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / p.block) (buffer : a.location.buffer = 0)
      (epoch : a.epoch.block = 1) (read : a.write = false)
  | scaleStore (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / p.block) (buffer : a.location.buffer = 1)
      (offset : a.location.offset = 0) (thread : a.thread % p.block = 0)
      (epoch : a.epoch.block = 1) (write : a.write = true)
  | scaleLoad (space : a.location.space = .shared)
      (owner : a.location.owner = a.thread / p.block) (buffer : a.location.buffer = 1)
      (offset : a.location.offset = 0) (epoch : a.epoch.block = 2) (read : a.write = false)

theorem partial_threads_eq (block a b : Nat)
    (owner : a / block = b / block) (slot : (a % block) / 64 = (b % block) / 64)
    (laneA : (a % block) % 64 = 0) (laneB : (b % block) % 64 = 0) : a = b := by
  have ha := Nat.div_add_mod (a % block) 64
  have hb := Nat.div_add_mod (b % block) 64
  simp only [laneA, Nat.add_zero] at ha
  simp only [laneB, Nat.add_zero] at hb
  rewrite [slot] at ha
  have hm : a % block = b % block := by omega
  have ha := Nat.div_add_mod a block
  have hb := Nat.div_add_mod b block
  rewrite [owner, hm] at ha
  omega

theorem scale_threads_eq (block a b : Nat) (owner : a / block = b / block)
    (laneA : a % block = 0) (laneB : b % block = 0) : a = b := by
  have ha := Nat.div_add_mod a block
  have hb := Nat.div_add_mod b block
  rewrite [owner, laneA] at ha
  rewrite [laneB] at hb
  omega

theorem ordered_blocks (p : LarkVectorStride.Shape) (a b : Access)
    (block : a.thread / p.block = b.thread / p.block)
    (epochs : a.epoch.block ≠ b.epoch.block) : ordered (geometry p) a b = true := by
  simp [ordered, geometry, block, epochs]

theorem collision (p : LarkVectorStride.Shape) (outBuffer : Nat) (a b : Access)
    (ha : Good p outBuffer a) (hb : Good p outBuffer b) (same : a.location = b.location) :
    a.thread = b.thread ∨ (a.write = false ∧ b.write = false) ∨ ordered (geometry p) a b = true := by
  have hs := congrArg Location.space same
  have ho := congrArg Location.owner same
  have hf := congrArg Location.buffer same
  have hi := congrArg Location.offset same
  cases ha <;> cases hb <;> simp_all
  case partialStore.partialStore =>
    left
    apply partial_threads_eq p.block a.thread b.thread <;> omega
  case partialStore.partialLoad =>
    right
    apply ordered_blocks p a b <;> omega
  case partialLoad.partialStore =>
    right
    apply ordered_blocks p a b <;> omega
  case scaleStore.scaleStore =>
    left
    apply scale_threads_eq p.block a.thread b.thread <;> omega
  case scaleStore.scaleLoad =>
    right
    apply ordered_blocks p a b <;> omega
  case scaleLoad.scaleStore =>
    right
    apply ordered_blocks p a b <;> omega

theorem sameLocation_true_iff (a b : Location) : sameLocation a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameLocation, Bool.and_eq_true, Location.mk.injEq, and_assoc]

theorem conflict_false (p : LarkVectorStride.Shape) (outBuffer : Nat) (a b : Access)
    (ha : Good p outBuffer a) (hb : Good p outBuffer b) : conflict (geometry p) a b = false := by
  by_cases hs : a.location = b.location
  · rcases collision p outBuffer a b ha hb hs with ht | hr | ho
    · simp [conflict, ht]
    · simp [conflict, hr.1, hr.2]
    · simp [conflict, ho]
  · have hl : sameLocation a.location b.location = false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (hs ((sameLocation_true_iff _ _).mp h))
    simp [conflict, hl]

/-- This discharges RF from locally proved accesses, without assuming RF. -/
theorem race_free (p : LarkVectorStride.Shape) (outBuffer : Nat) (trace : List Access)
    (good : ∀ a ∈ trace, Good p outBuffer a) : raceFree (geometry p) trace = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [conflict_false p outBuffer a b (good a ha) (good b hb)]

#print axioms partial_threads_eq
#print axioms race_free
end LarkReductionFootprint
