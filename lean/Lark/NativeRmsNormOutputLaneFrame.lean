import Lark.NativeRmsNormOutputFrame
import Lark.NativeRmsNormOutputLane

/-! Complete output-lane frames and exact values at its sixteen owned cells. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem output_pair_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location)
    (h0 : ∀ c, c < 8 → l ≠ globalCell 0 (scalarAddress row tid c))
    (h1 : ∀ c, c < 8 → l ≠ globalCell 0 (scalarAddress row (tid + 1024) c)) :
    (outputPair ops input row tid t inverse s).memory l = s.memory l :=
  (output_vector_memory_other ops input row (tid + 1024) t inverse
    (outputVector ops input row tid t inverse s) l h1).trans
    (output_vector_memory_other ops input row tid t inverse s l h0)

theorem output_pair_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputPair ops input row tid t inverse s) :=
  output_vector_reads p ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s)
    (output_vector_reads p ops input row tid t inverse s reads)

theorem output_pair_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (outputPair ops input row tid t inverse s).epochs = s.epochs :=
  (output_vector_fields ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s)).2.2.2.2.trans
    (output_vector_fields ops input row tid t inverse s).2.2.2.2

theorem output_pair_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u r : Nat) (inverse : α) (s : State α) (hr7 : r ≠ 7) (hr8 : r ≠ 8) :
    (outputPair ops input row tid t inverse s).indices u r = s.indices u r :=
  (output_vector_index_frame ops input row (tid + 1024) t u r inverse
    (outputVector ops input row tid t inverse s) hr7 hr8).trans
    (output_vector_index_frame ops input row tid t u r inverse s hr7 hr8)

theorem output_pair_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputPair ops input row tid t inverse s).pc u = s.pc u ∧
    (outputPair ops input row tid t inverse s).indices u = s.indices u ∧
    (outputPair ops input row tid t inverse s).regs u = s.regs u := by
  have h0 := output_vector_other ops input row tid t u inverse s hu
  have h1 := output_vector_other ops input row (tid + 1024) t u inverse (outputVector ops input row tid t inverse s) hu
  exact ⟨h1.1.trans h0.1, h1.2.1.trans h0.2.1, h1.2.2.trans h0.2.2⟩

theorem output_pair_value_first (ops : Ops α) (input : Nat → Nat → α)
    (row tid t c : Nat) (inverse : α) (s : State α) (hc : c < 8) :
    (outputPair ops input row tid t inverse s).memory (globalCell 0 (scalarAddress row tid c)) =
      some (ops.toHalf (outputWeighted ops input row tid c inverse)) := by
  have h := output_vector_memory_other ops input row (tid + 1024) t inverse (outputVector ops input row tid t inverse s)
    (globalCell 0 (scalarAddress row tid c))
    (by intro d hd; exact scalar_vector_ne row tid (tid + 1024) c d hc hd (by omega))
  exact h.trans (output_vector_value ops input row tid t c inverse s hc)

theorem output_pair_value_second (ops : Ops α) (input : Nat → Nat → α)
    (row tid t c : Nat) (inverse : α) (s : State α) (hc : c < 8) :
    (outputPair ops input row tid t inverse s).memory (globalCell 0 (scalarAddress row (tid + 1024) c)) =
      some (ops.toHalf (outputWeighted ops input row (tid + 1024) c inverse)) :=
  output_vector_value ops input row (tid + 1024) t c inverse (outputVector ops input row tid t inverse s) hc

theorem output_lane_pc (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (s : State α) :
    (outputLane ops input row tid t s).pc t = 70 := by simp [outputLane, advance]

theorem output_lane_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (reads : Reads p input s) : Reads p input (outputLane ops input row tid t s) :=
  output_pair_reads p ops input row tid t (scale ops input row) (outEntered t row tid (scale ops input row) s) reads

theorem output_lane_epochs (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (s : State α) :
    (outputLane ops input row tid t s).epochs = s.epochs :=
  (output_pair_epochs ops input row tid t (scale ops input row) (outEntered t row tid (scale ops input row) s)).trans
    (output_entry_preserves t row tid (scale ops input row) s).2

theorem output_lane_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u r : Nat) (s : State α) (hr7 : r ≠ 7) (hr8 : r ≠ 8) :
    (outputLane ops input row tid t s).indices u r = s.indices u r :=
  (output_pair_index_frame ops input row tid t u r (scale ops input row)
    (outEntered t row tid (scale ops input row) s) hr7 hr8).trans
    (by simp [outEntered, outLoaded, setIndex, setReg, advance, record, hr7])

theorem output_lane_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t u : Nat) (s : State α) (hu : u ≠ t) :
    (outputLane ops input row tid t s).pc u = s.pc u ∧
    (outputLane ops input row tid t s).indices u = s.indices u ∧
    (outputLane ops input row tid t s).regs u = s.regs u := by
  have h0 := output_entry_other t u row tid (scale ops input row) s hu
  have h1 := output_pair_other ops input row tid t u (scale ops input row) (outEntered t row tid (scale ops input row) s) hu
  refine ⟨?_, h1.2.1.trans h0.2.1, h1.2.2.trans h0.2.2⟩
  exact (show (outputLane ops input row tid t s).pc u =
    (outputPair ops input row tid t (scale ops input row) (outEntered t row tid (scale ops input row) s)).pc u by
      simp only [outputLane, advance, if_neg hu]).trans (h1.1.trans h0.1)

theorem output_lane_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (s : State α) (l : Location)
    (h0 : ∀ c, c < 8 → l ≠ globalCell 0 (scalarAddress row tid c))
    (h1 : ∀ c, c < 8 → l ≠ globalCell 0 (scalarAddress row (tid + 1024) c)) :
    (outputLane ops input row tid t s).memory l = s.memory l :=
  (output_pair_memory_other ops input row tid t (scale ops input row) (outEntered t row tid (scale ops input row) s) l h0 h1).trans
    (congrFun (output_entry_preserves t row tid (scale ops input row) s).1 l)

theorem output_lane_value (ops : Ops α) (input : Nat → Nat → α)
    (row tid t c : Nat) (s : State α) (hc : c < 8) :
    (outputLane ops input row tid t s).memory (globalCell 0 (scalarAddress row tid c)) =
      some (ops.toHalf (outputWeighted ops input row tid c (scale ops input row))) ∧
    (outputLane ops input row tid t s).memory (globalCell 0 (scalarAddress row (tid + 1024) c)) =
      some (ops.toHalf (outputWeighted ops input row (tid + 1024) c (scale ops input row))) :=
  ⟨output_pair_value_first ops input row tid t c (scale ops input row) (outEntered t row tid (scale ops input row) s) hc,
   output_pair_value_second ops input row tid t c (scale ops input row) (outEntered t row tid (scale ops input row) s) hc⟩

#print axioms output_lane_other
#print axioms output_lane_memory_other
#print axioms output_lane_index_frame
#print axioms output_lane_value
end LarkNativeRmsNorm
