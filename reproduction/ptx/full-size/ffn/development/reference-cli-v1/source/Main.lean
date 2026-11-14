import Lark.PtxFeedForwardReference
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkCompiledFfnReferenceInput
open LarkNonlinear LarkPtxFeedForward.Reference
def body : TensorReference := (.toHalf (.matmul (.fromHalf (.toHalf (.relu (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1)))))) (.fromHalf (.input 2))))
theorem reference_body : body = referenceBody := by rfl
theorem reference_denotation (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 16384) :
    (match evaluate ops input body with
     | some tensor => tensor.cell t
     | none => none) = some (outputValue ops input t) := by
  rw [reference_body, evaluate_body]
  exact reference_cell ops input t ht
theorem reference_extraction (ops : Ops α) (input : Nat → Nat → α) :
    extractReference ops input body = some (referenceSpec ops input) := by
  exact extract_evaluated_tensor ops input body (referenceTensor ops input) (outputValue ops input)
    (by rw [reference_body]; exact evaluate_body ops input)
    (reference_shape ops input) (reference_cell ops input)
#print axioms reference_body
#print axioms reference_denotation
#print axioms reference_extraction
end LarkCompiledFfnReferenceInput
