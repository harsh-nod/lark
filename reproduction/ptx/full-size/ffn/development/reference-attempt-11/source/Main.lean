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
#print axioms reference_body
#print axioms reference_denotation
end LarkCompiledFfnReferenceInput
