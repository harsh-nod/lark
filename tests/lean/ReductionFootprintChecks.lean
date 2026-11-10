import Lark.ReductionFootprint
namespace ReductionFootprintChecks
open LarkNonlinear LarkReductionFootprint
set_option maxRecDepth 10000

def shape : LarkVectorStride.Shape :=
  ⟨2, 16384, 1024, 8, by decide, by decide, by decide, by decide, by decide, by decide⟩
def partialWrite : Access := ⟨64, ⟨.shared, 0, 0, 1⟩, true, ⟨0, 0, 0⟩⟩
def partialRead : Access := ⟨0, ⟨.shared, 0, 0, 1⟩, false, ⟨0, 1, 0⟩⟩
def scaleWrite : Access := ⟨0, ⟨.shared, 0, 1, 0⟩, true, ⟨0, 1, 0⟩⟩
def scaleRead : Access := ⟨64, ⟨.shared, 0, 1, 0⟩, false, ⟨0, 2, 0⟩⟩
def inputRead : Access := ⟨64, ⟨.global, 0, 1, 512⟩, false, ⟨0, 2, 0⟩⟩
def outputWrite : Access := ⟨64, ⟨.global, 0, 0, 512⟩, true, ⟨0, 2, 0⟩⟩
def trace : List Access := [partialWrite, partialRead, scaleWrite, scaleRead, inputRead, outputWrite]

theorem classified : ∀ a ∈ trace, Good shape 0 a := by
  intro a ha
  simp [trace] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .partialStore rfl rfl rfl rfl rfl rfl rfl
  · exact .partialLoad rfl rfl rfl rfl rfl
  · exact .scaleStore rfl rfl rfl rfl rfl rfl rfl
  · exact .scaleLoad rfl rfl rfl rfl rfl rfl
  · exact .input rfl rfl (by decide) rfl
  · exact .output rfl rfl rfl rfl rfl

theorem safe_trace : raceFree (geometry shape) trace = true := race_free shape 0 trace classified

theorem missing_barrier_conflicts :
    conflict (geometry shape) partialWrite { partialRead with epoch := ⟨0, 0, 0⟩ } = true := by rfl

theorem duplicate_partial_writer_conflicts :
    conflict (geometry shape) partialWrite { partialWrite with thread := 65 } = true := by rfl

theorem wrong_output_owner_conflicts :
    conflict (geometry shape) outputWrite { outputWrite with thread := 128 } = true := by rfl

theorem last_vector_cell :
    LarkVectorStride.column shape 1023 1 7 = 16383 ∧
    LarkVectorStride.writer shape 32767 = 2047 := by decide

#print axioms classified
#print axioms safe_trace
#print axioms missing_barrier_conflicts
#print axioms duplicate_partial_writer_conflicts
#print axioms wrong_output_owner_conflicts
#print axioms last_vector_cell
end ReductionFootprintChecks
