import Lark.NativeRmsNormOutputLaneFrame

/-! An output lane changes only global output locations assigned to its unique
native writer. The property also frames arbitrary outside memory.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def OutputOwner (p : Shape) (t : Nat) (l : Location) : Prop :=
  l.space = .global ∧ l.owner = 0 ∧ l.buffer = 0 ∧ LarkVectorStride.writer (traversal p) l.offset = t

theorem output_cell_owner (p : Shape) (row tid t vector c : Nat) (hv : vector < 2048) (hc : c < 8)
    (hm : vector % 1024 = tid) (ht : t = row * 1024 + tid) :
    OutputOwner p t (globalCell 0 (scalarAddress row vector c)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact (output_writer p row vector c hv hc).trans (by rewrite [hm]; exact ht.symm)

theorem output_lane_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (ht : tid < 1024) (hthread : t = row * 1024 + tid)
    (l : Location) (hl : ¬ OutputOwner p t l) :
    (outputLane ops input row tid t s).memory l = s.memory l := by
  apply output_lane_memory_other ops input row tid t s l
  · intro c hc he
    subst l
    exact hl (output_cell_owner p row tid t tid c (by omega) hc (Nat.mod_eq_of_lt ht) hthread)
  · intro c hc he
    subst l
    exact hl (output_cell_owner p row tid t (tid + 1024) c (by omega) hc
      (by simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt ht]) hthread)

theorem output_owner_ne (p : Shape) (t u : Nat) (l : Location) (ht : OutputOwner p t l) (hne : t ≠ u) :
    ¬ OutputOwner p u l := by
  intro hu
  exact hne (ht.2.2.2.symm.trans hu.2.2.2)

theorem output_lane_native_indices (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (s : State α) (hi : NativeIndices u s) :
    NativeIndices u (outputLane ops input row tid t s) := by
  unfold NativeIndices at hi ⊢
  simpa only [output_lane_index_frame ops input row tid t u 0 s (by decide) (by decide),
    output_lane_index_frame ops input row tid t u 1 s (by decide) (by decide),
    output_lane_index_frame ops input row tid t u 2 s (by decide) (by decide),
    output_lane_index_frame ops input row tid t u 3 s (by decide) (by decide),
    output_lane_index_frame ops input row tid t u 4 s (by decide) (by decide)] using hi

theorem output_lane_scale_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (ht : tid < 1024) (hthread : t = row * 1024 + tid) :
    (outputLane ops input row tid t s).memory (scaleSlot row) = s.memory (scaleSlot row) :=
  output_lane_memory_frame p ops input row tid t s ht hthread (scaleSlot row) (by
    intro h
    have h := h.1
    simp [scaleSlot] at h)

#print axioms output_lane_memory_frame
#print axioms output_lane_native_indices
end LarkNativeRmsNorm
