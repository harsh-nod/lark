import Lark.Nonlinear

/-!
Independent tensor semantics for the complete 64x256x1024x256 FP16 FFN
reference. Matmul reads the actual input cells, accumulates in increasing
reduction-index order and checks the dimensions. Both half conversions around
the intermediate remain explicit. This module proves reference denotation;
it contains no PTX program or compiled-kernel correctness assumption.
-/
namespace LarkPtxFeedForward.Reference
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Tensor (α : Type) where
  rows : Nat
  columns : Nat
  cell : Nat → Option α

def emptyTensor : Tensor α := ⟨0, 0, fun _ => none⟩

def mapTensor (f : α → α) (a : Tensor α) : Tensor α :=
  ⟨a.rows, a.columns, fun i => f <$> a.cell i⟩

def inputTensor (input : Nat → Nat → α) (slot : Nat) : Option (Tensor α) :=
  match slot with
  | 0 => some ⟨64, 256, fun i => if i < 16384 then some (input 0 i) else none⟩
  | 1 => some ⟨256, 1024, fun i => if i < 262144 then some (input 1 i) else none⟩
  | 2 => some ⟨1024, 256, fun i => if i < 262144 then some (input 2 i) else none⟩
  | _ => none

def dot (ops : Ops α) (a b : Tensor α) (row column k r : Nat) (acc : α) : Option α :=
  (Nat.rec (motive := fun _ => Nat → α → Option α)
    (fun _ acc => some acc)
    (fun _ next k acc => do
      let x ← a.cell (row*a.columns+k)
      let y ← b.cell (k*b.columns+column)
      next (k+1) (ops.add acc (ops.mul x y))) r) k acc

def multiply (ops : Ops α) (a b : Tensor α) : Option (Tensor α) :=
  if a.columns = b.rows then
    some ⟨a.rows, b.columns, fun i => if i < a.rows*b.columns then
      dot ops a b (i/b.columns) (i%b.columns) 0 a.columns (ops.literal 0 1) else none⟩
  else none

theorem multiply_cell (ops : Ops α) (a b : Tensor α) (i : Nat)
    (hd : a.columns = b.rows) (hi : i < a.rows*b.columns) :
    ((multiply ops a b).getD emptyTensor).cell i =
      dot ops a b (i/b.columns) (i%b.columns) 0 a.columns (ops.literal 0 1) := by
  simp [multiply, hd, hi]

inductive TensorReference where
  | input : Nat → TensorReference
  | fromHalf : TensorReference → TensorReference
  | toHalf : TensorReference → TensorReference
  | relu : TensorReference → TensorReference
  | matmul : TensorReference → TensorReference → TensorReference
  deriving DecidableEq, Repr

def evaluate (ops : Ops α) (input : Nat → Nat → α) : TensorReference → Option (Tensor α)
  | .input slot => inputTensor input slot
  | .fromHalf a => do
      let a ← evaluate ops input a
      pure (mapTensor ops.fromHalf a)
  | .toHalf a => do
      let a ← evaluate ops input a
      pure (mapTensor ops.toHalf a)
  | .relu a => do
      let a ← evaluate ops input a
      pure (mapTensor (fun x => ops.max x (ops.literal 0 1)) a)
  | .matmul a b => do
      let a ← evaluate ops input a
      let b ← evaluate ops input b
      multiply ops a b

def upBody : TensorReference :=
  .toHalf (.relu (.matmul (.fromHalf (.input 0)) (.fromHalf (.input 1))))

def referenceBody : TensorReference :=
  .toHalf (.matmul (.fromHalf upBody) (.fromHalf (.input 2)))

def tensorAt (input : Nat → Nat → α) (slot : Nat) : Tensor α :=
  (inputTensor input slot).getD emptyTensor

def upProduct (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  (multiply ops (mapTensor ops.fromHalf (tensorAt input 0))
    (mapTensor ops.fromHalf (tensorAt input 1))).getD emptyTensor

def hiddenTensor (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  mapTensor ops.toHalf (mapTensor (fun x => ops.max x (ops.literal 0 1)) (upProduct ops input))

def downProduct (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  (multiply ops (mapTensor ops.fromHalf (hiddenTensor ops input))
    (mapTensor ops.fromHalf (tensorAt input 2))).getD emptyTensor

def referenceTensor (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  mapTensor ops.toHalf (downProduct ops input)

theorem evaluate_up (ops : Ops α) (input : Nat → Nat → α) :
    evaluate ops input upBody = some (hiddenTensor ops input) := rfl

theorem evaluate_body (ops : Ops α) (input : Nat → Nat → α) :
    evaluate ops input referenceBody = some (referenceTensor ops input) := rfl

theorem hidden_shape (ops : Ops α) (input : Nat → Nat → α) :
    (hiddenTensor ops input).rows = 64 ∧ (hiddenTensor ops input).columns = 1024 := by
  exact ⟨rfl, rfl⟩

theorem reference_shape (ops : Ops α) (input : Nat → Nat → α) :
    (referenceTensor ops input).rows = 64 ∧ (referenceTensor ops input).columns = 256 := by
  exact ⟨rfl, rfl⟩

def scalarFold (term : Nat → α → α) (k r : Nat) (acc : α) : α :=
  (Nat.rec (motive := fun _ => Nat → α → α)
    (fun _ acc => acc)
    (fun _ next k acc => next (k+1) (term k acc)) r) k acc

theorem dot_fold (ops : Ops α) (a b : Tensor α) (row column k r : Nat) (acc : α)
    (left right : Nat → α)
    (ha : ∀ j, k ≤ j → j < k+r → a.cell (row*a.columns+j) = some (left j))
    (hb : ∀ j, k ≤ j → j < k+r → b.cell (j*b.columns+column) = some (right j)) :
    dot ops a b row column k r acc =
      some (scalarFold (fun j v => ops.add v (ops.mul (left j) (right j))) k r acc) := by
  revert ha hb
  induction r generalizing k acc with
  | zero => intros; rfl
  | succ r ih =>
      intro ha hb
      simp only [dot, scalarFold, ha k (by omega) (by omega), hb k (by omega) (by omega),
        Option.bind_some]
      exact ih (k+1) (ops.add acc (ops.mul (left k) (right k)))
        (fun j hj hk => ha j (by omega) (by omega))
        (fun j hj hk => hb j (by omega) (by omega))

theorem multiply_fold (ops : Ops α) (a b : Tensor α) (i : Nat)
    (hd : a.columns = b.rows) (hi : i < a.rows*b.columns)
    (left right : Nat → α) (term : Nat → α → α)
    (hterm : (fun j v => ops.add v (ops.mul (left j) (right j))) = term)
    (ha : ∀ j, j < a.columns → a.cell (i/b.columns*a.columns+j) = some (left j))
    (hb : ∀ j, j < a.columns → b.cell (j*b.columns+i%b.columns) = some (right j)) :
    ((multiply ops a b).getD emptyTensor).cell i =
      some (scalarFold term 0 a.columns (ops.literal 0 1)) := by
  have hf := dot_fold ops a b (i/b.columns) (i%b.columns) 0 a.columns (ops.literal 0 1)
    left right (fun j _ hj => ha j (by omega)) (fun j _ hj => hb j (by omega))
  exact (multiply_cell ops a b i hd hi).trans
    (hf.trans (congrArg (fun f => some (scalarFold f 0 a.columns (ops.literal 0 1))) hterm))

theorem mapped_multiply_fold (ops : Ops α) (post : α → α) (a b : Tensor α) (i k : Nat)
    (hk : a.columns = k)
    (hd : a.columns = b.rows) (hi : i < a.rows*b.columns)
    (left right : Nat → α) (term : Nat → α → α)
    (hterm : (fun j v => ops.add v (ops.mul (left j) (right j))) = term)
    (ha : ∀ j, j < a.columns → a.cell (i/b.columns*a.columns+j) = some (left j))
    (hb : ∀ j, j < a.columns → b.cell (j*b.columns+i%b.columns) = some (right j)) :
    (mapTensor post ((multiply ops a b).getD emptyTensor)).cell i =
      some (post (scalarFold term 0 k (ops.literal 0 1))) := by
  have h := congrArg (fun value : Option α => post <$> value)
    (multiply_fold ops a b i hd hi left right term hterm ha hb)
  simpa only [hk] using h

theorem double_mapped_multiply_fold (ops : Ops α) (post1 post2 : α → α)
    (a b : Tensor α) (i k : Nat)
    (hk : a.columns = k)
    (hd : a.columns = b.rows) (hi : i < a.rows*b.columns)
    (left right : Nat → α) (term : Nat → α → α)
    (hterm : (fun j v => ops.add v (ops.mul (left j) (right j))) = term)
    (ha : ∀ j, j < a.columns → a.cell (i/b.columns*a.columns+j) = some (left j))
    (hb : ∀ j, j < a.columns → b.cell (j*b.columns+i%b.columns) = some (right j)) :
    (mapTensor post1 (mapTensor post2 ((multiply ops a b).getD emptyTensor))).cell i =
      some (post1 (post2 (scalarFold term 0 k (ops.literal 0 1)))) := by
  have h := congrArg (fun value : Option α => post1 <$> (post2 <$> value))
    (multiply_fold ops a b i hd hi left right term hterm ha hb)
  simpa only [hk] using h

#print dot
#print scalarFold

abbrev upTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/1024*256+k)))
    (ops.fromHalf (input 1 (k*1024+t%1024))))

def hiddenValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (ops.max (scalarFold (upTerm ops input t) 0 256 (ops.literal 0 1)) (ops.literal 0 1))

theorem hidden_cell (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 65536) :
    (hiddenTensor ops input).cell t = some (hiddenValue ops input t) := by
  exact double_mapped_multiply_fold ops ops.toHalf (fun x => ops.max x (ops.literal 0 1))
    (mapTensor ops.fromHalf (tensorAt input 0))
    (mapTensor ops.fromHalf (tensorAt input 1)) t 256 (by rfl) (by rfl) ht
    (fun j => ops.fromHalf (input 0 (t/1024*256+j)))
    (fun j => ops.fromHalf (input 1 (j*1024+t%1024)))
    (upTerm ops input t) (by rfl)
    (by
      intro j hj
      change j < 256 at hj
      have h : t/1024*256+j < 16384 := by omega
      simp [mapTensor, tensorAt, inputTensor, h])
    (by
      intro j hj
      change j < 256 at hj
      have h : j*1024+t%1024 < 262144 := by omega
      simp [mapTensor, tensorAt, inputTensor, h])

abbrev downTerm (ops : Ops α) (input : Nat → Nat → α) (t k : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (hiddenValue ops input (t/256*1024+k)))
    (ops.fromHalf (input 2 (k*256+t%256))))

def outputValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (scalarFold (downTerm ops input t) 0 1024 (ops.literal 0 1))

theorem reference_cell (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 16384) :
    (referenceTensor ops input).cell t = some (outputValue ops input t) := by
  exact mapped_multiply_fold ops ops.toHalf (mapTensor ops.fromHalf (hiddenTensor ops input))
    (mapTensor ops.fromHalf (tensorAt input 2)) t 1024 (by rfl) (by rfl) ht
    (fun j => ops.fromHalf (hiddenValue ops input (t/256*1024+j)))
    (fun j => ops.fromHalf (input 2 (j*256+t%256)))
    (downTerm ops input t) (by rfl)
    (by
      intro j hj
      change j < 1024 at hj
      have h : t/256*1024+j < 65536 := by omega
      change ops.fromHalf <$> (hiddenTensor ops input).cell (t/256*1024+j) = _
      rw [hidden_cell ops input _ h]
      rfl)
    (by
      intro j hj
      change j < 1024 at hj
      have h : j*256+t%256 < 262144 := by omega
      simp [mapTensor, tensorAt, inputTensor, h])

theorem reference_outside (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : 16384 ≤ t) :
    (referenceTensor ops input).cell t = none := by
  change ops.toHalf <$> (if t < 16384 then _ else none) = none
  simp [Nat.not_lt.mpr ht]

#print axioms evaluate_up
#print axioms multiply_cell
#print axioms evaluate_body
#print axioms hidden_shape
#print axioms reference_shape
#print axioms dot_fold
#print axioms multiply_fold
#print axioms mapped_multiply_fold
#print axioms double_mapped_multiply_fold
#print axioms hidden_cell
#print axioms reference_cell
#print axioms reference_outside
end LarkPtxFeedForward.Reference
