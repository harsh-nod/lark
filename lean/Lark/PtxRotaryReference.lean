import Lark.PtxRotaryKernel

/-!
Independent tensor-expression semantics for the complete original interleaved
RoPE reference. Reshape preserves linear data after an element-count check;
select and stack compute their actual flattened indices. Arithmetic and both
half conversions retain their original order. No PTX program is evaluated here.
-/
namespace LarkPtxRotary
namespace Reference
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Tensor (α : Type) where
  shape : List Nat
  cell : Nat → Option α

def elements (shape : List Nat) : Nat := shape.foldr (· * ·) 1

def mapTensor (f : α → α) (t : Tensor α) : Tensor α :=
  ⟨t.shape, fun i => f <$> t.cell i⟩

def binaryTensor (ops : Ops α) (op : Binary) (a b : Tensor α) : Option (Tensor α) :=
  if a.shape = b.shape then
    some ⟨a.shape, fun i => do
      let x ← a.cell i
      let y ← b.cell i
      pure (applyBinary ops op x y)⟩
  else none

inductive TensorReference where
  | input : Nat → TensorReference
  | fromHalf : TensorReference → TensorReference
  | toHalf : TensorReference → TensorReference
  | reshape : List Nat → TensorReference → TensorReference
  | select : Nat → Nat → TensorReference → TensorReference
  | binary : Binary → TensorReference → TensorReference → TensorReference
  | stackLast : TensorReference → TensorReference → TensorReference
  deriving DecidableEq, Repr

def evaluate (ops : Ops α) (input : Nat → Nat → α) : TensorReference → Option (Tensor α)
  | .input 0 => some ⟨[256, 128], fun i => if i < 32768 then some (input 0 i) else none⟩
  | .input 1 => some ⟨[256, 64], fun i => if i < 16384 then some (input 1 i) else none⟩
  | .input 2 => some ⟨[256, 64], fun i => if i < 16384 then some (input 2 i) else none⟩
  | .input _ => none
  | .fromHalf a => do
      let a ← evaluate ops input a
      pure (mapTensor ops.fromHalf a)
  | .toHalf a => do
      let a ← evaluate ops input a
      pure (mapTensor ops.toHalf a)
  | .reshape shape a => do
      let a ← evaluate ops input a
      if elements shape = elements a.shape then some ⟨shape, a.cell⟩ else none
  | .select axis index a => do
      let a ← evaluate ops input a
      match a.shape with
      | [m, n, 2] =>
          if axis = 2 ∧ index < 2 then
            some ⟨[m, n], fun i => if i < m*n then a.cell (i*2+index) else none⟩
          else none
      | _ => none
  | .binary op a b => do
      let a ← evaluate ops input a
      let b ← evaluate ops input b
      binaryTensor ops op a b
  | .stackLast a b => do
      let a ← evaluate ops input a
      let b ← evaluate ops input b
      if a.shape = b.shape then
        match a.shape with
        | [m, n] =>
            some ⟨[m, n, 2], fun i => if i < m*n*2 then
              if i%2 = 0 then a.cell (i/2) else b.cell (i/2) else none⟩
        | _ => none
      else none

def evenInput : TensorReference :=
  .select 2 0 (.reshape [256, 64, 2] (.fromHalf (.input 0)))
def oddInput : TensorReference :=
  .select 2 1 (.reshape [256, 64, 2] (.fromHalf (.input 0)))
def referenceBody : TensorReference :=
  .toHalf (.reshape [256, 128] (.stackLast
    (.binary .sub (.binary .mul evenInput (.fromHalf (.input 1)))
      (.binary .mul oddInput (.fromHalf (.input 2))))
    (.binary .add (.binary .mul evenInput (.fromHalf (.input 2)))
      (.binary .mul oddInput (.fromHalf (.input 1))))))

def referenceTensor (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  (evaluate ops input referenceBody).getD ⟨[], fun _ => none⟩

theorem evaluate_body (ops : Ops α) (input : Nat → Nat → α) :
    evaluate ops input referenceBody = some (referenceTensor ops input) := rfl

theorem reference_shape (ops : Ops α) (input : Nat → Nat → α) :
    (referenceTensor ops input).shape = [256, 128] := rfl

theorem reference_cell (ops : Ops α) (input : Nat → Nat → α) (i : Nat) (hi : i < 32768) :
    (referenceTensor ops input).cell i = some (Kernel.reference ops input i) := by
  have hp : i/2 < 16384 := by omega
  have hx0 : i/2*2 < 32768 := by omega
  have hx1 : i/2*2+1 < 32768 := by omega
  by_cases he : i%2 = 0 <;>
    simp [referenceTensor, referenceBody, evenInput, oddInput, evaluate, mapTensor,
      binaryTensor, elements, applyBinary, Kernel.reference, hi, hp, hx0, hx1, he]

def extractReference (ops : Ops α) (input : Nat → Nat → α) (body : TensorReference) : Option (List α) := do
  let tensor ← evaluate ops input body
  if tensor.shape = [256, 128] then (List.range 32768).mapM tensor.cell else none

theorem extract_evaluated_tensor (ops : Ops α) (input : Nat → Nat → α) (body : TensorReference)
    (tensor : Tensor α) (values : Nat → α)
    (he : evaluate ops input body = some tensor) (hs : tensor.shape = [256, 128])
    (hc : ∀ i, i < 32768 → tensor.cell i = some (values i)) :
    extractReference ops input body = some ((List.range 32768).map values) := by
  unfold extractReference
  rw [he]
  change (if tensor.shape = [256, 128] then (List.range 32768).mapM tensor.cell else none) = _
  rw [hs, if_pos rfl]
  exact LarkPointwise.mapM_some (List.range 32768) _ _ (by
    intro i hi
    exact hc i (List.mem_range.mp hi))

theorem extract_reference_body (ops : Ops α) (input : Nat → Nat → α) :
    extractReference ops input referenceBody = some (Kernel.referenceSpec ops input) :=
  extract_evaluated_tensor ops input referenceBody (referenceTensor ops input) (Kernel.reference ops input)
    (evaluate_body ops input) (reference_shape ops input) (reference_cell ops input)

def spec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (extractReference ops input referenceBody).getD []

theorem closed_reference_correct (ops : Ops α) : Kernel.Correct ops Kernel.program (spec ops) := by
  have hs : spec ops = Kernel.referenceSpec ops := by
    funext input
    simp [spec, extract_reference_body]
  rw [hs]
  exact Kernel.kernel_correct ops

#print axioms evaluate_body
#print axioms reference_shape
#print axioms reference_cell
#print axioms extract_evaluated_tensor
#print axioms extract_reference_body
#print axioms closed_reference_correct
end Reference
end LarkPtxRotary
