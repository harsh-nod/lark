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

def inputMatrix (input : Nat → Nat → α) (slot m n : Nat) : Tensor α :=
  ⟨m, n, fun i => if i < m*n then some (input slot i) else none⟩

def inputTensor (input : Nat → Nat → α) (slot : Nat) : Option (Tensor α) :=
  match slot with
  | 0 => some (inputMatrix input 0 64 256)
  | 1 => some (inputMatrix input 1 256 1024)
  | 2 => some (inputMatrix input 2 1024 256)
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

def upProductWith (ops : Ops α) (input : Nat → Nat → α) (m k h : Nat) : Tensor α :=
  (multiply ops (mapTensor ops.fromHalf (inputMatrix input 0 m k))
    (mapTensor ops.fromHalf (inputMatrix input 1 k h))).getD emptyTensor

def hiddenTensorWith (ops : Ops α) (input : Nat → Nat → α) (m k h : Nat) : Tensor α :=
  mapTensor ops.toHalf (mapTensor (fun x => ops.max x (ops.literal 0 1)) (upProductWith ops input m k h))

def downProductWith (ops : Ops α) (input : Nat → Nat → α) (m k h n : Nat) : Tensor α :=
  (multiply ops (mapTensor ops.fromHalf (hiddenTensorWith ops input m k h))
    (mapTensor ops.fromHalf (inputMatrix input 2 h n))).getD emptyTensor

def referenceTensorWith (ops : Ops α) (input : Nat → Nat → α) (m k h n : Nat) : Tensor α :=
  mapTensor ops.toHalf (downProductWith ops input m k h n)

def upProduct (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  upProductWith ops input 64 256 1024

def hiddenTensor (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  hiddenTensorWith ops input 64 256 1024

def downProduct (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  downProductWith ops input 64 256 1024 256

def referenceTensor (ops : Ops α) (input : Nat → Nat → α) : Tensor α :=
  referenceTensorWith ops input 64 256 1024 256

theorem hiddenWith_shape (ops : Ops α) (input : Nat → Nat → α) (m k h : Nat) :
    (hiddenTensorWith ops input m k h).rows = m ∧
      (hiddenTensorWith ops input m k h).columns = h := by
  simp [hiddenTensorWith, upProductWith, multiply, mapTensor, inputMatrix]

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

theorem row_major_bound (m n row column : Nat) (hr : row < m) (hc : column < n) :
    row*n+column < m*n := by
  calc
    row*n+column < row*n+n := Nat.add_lt_add_left hc _
    _ = (row+1)*n := by simp [Nat.add_mul]
    _ ≤ m*n := Nat.mul_le_mul_right n (by omega)

abbrev upTermWith (ops : Ops α) (input : Nat → Nat → α) (k h t j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (input 0 (t/h*k+j)))
    (ops.fromHalf (input 1 (j*h+t%h))))

def hiddenValueWith (ops : Ops α) (input : Nat → Nat → α) (k h t : Nat) : α :=
  ops.toHalf (ops.max (scalarFold (upTermWith ops input k h t) 0 k (ops.literal 0 1)) (ops.literal 0 1))

theorem hiddenWith_cell (ops : Ops α) (input : Nat → Nat → α) (m k h t : Nat)
    (hh : 0 < h) (ht : t < m*h) :
    (hiddenTensorWith ops input m k h).cell t = some (hiddenValueWith ops input k h t) := by
  exact double_mapped_multiply_fold ops ops.toHalf (fun x => ops.max x (ops.literal 0 1))
    (mapTensor ops.fromHalf (inputMatrix input 0 m k))
    (mapTensor ops.fromHalf (inputMatrix input 1 k h)) t k (by rfl) (by rfl) ht
    (fun j => ops.fromHalf (input 0 (t/h*k+j)))
    (fun j => ops.fromHalf (input 1 (j*h+t%h)))
    (upTermWith ops input k h t) (by rfl)
    (by
      intro j hj
      change j < k at hj
      have hr : t/h < m := (Nat.div_lt_iff_lt_mul hh).mpr ht
      have hab := row_major_bound m k (t/h) j hr hj
      simp [mapTensor, inputMatrix, hab])
    (by
      intro j hj
      change j < k at hj
      have hbb := row_major_bound k h j (t%h) hj (Nat.mod_lt t hh)
      simp [mapTensor, inputMatrix, hbb])

abbrev downTermWith (ops : Ops α) (input : Nat → Nat → α) (k h n t j : Nat) (acc : α) : α :=
  ops.add acc (ops.mul (ops.fromHalf (hiddenValueWith ops input k h (t/n*h+j)))
    (ops.fromHalf (input 2 (j*n+t%n))))

def outputValueWith (ops : Ops α) (input : Nat → Nat → α) (k h n t : Nat) : α :=
  ops.toHalf (scalarFold (downTermWith ops input k h n t) 0 h (ops.literal 0 1))

theorem referenceWith_cell (ops : Ops α) (input : Nat → Nat → α) (m k h n t : Nat)
    (hh : 0 < h) (hn : 0 < n) (ht : t < m*n) :
    (referenceTensorWith ops input m k h n).cell t = some (outputValueWith ops input k h n t) := by
  have hrows := (hiddenWith_shape ops input m k h).1
  have hcols := (hiddenWith_shape ops input m k h).2
  exact mapped_multiply_fold ops ops.toHalf (mapTensor ops.fromHalf (hiddenTensorWith ops input m k h))
    (mapTensor ops.fromHalf (inputMatrix input 2 h n)) t h
    (by simpa only [mapTensor] using hcols)
    (by simpa only [mapTensor, inputMatrix] using hcols)
    (by simpa only [mapTensor, inputMatrix, hrows] using ht)
    (fun j => ops.fromHalf (hiddenValueWith ops input k h (t/n*h+j)))
    (fun j => ops.fromHalf (input 2 (j*n+t%n)))
    (downTermWith ops input k h n t) (by rfl)
    (by
      intro j hj
      have hj' : j < h := by simpa only [mapTensor, hcols] using hj
      have hr : t/n < m := (Nat.div_lt_iff_lt_mul hn).mpr ht
      have hab := row_major_bound m h (t/n) j hr hj'
      simp only [mapTensor, inputMatrix, hcols]
      rw [hiddenWith_cell ops input m k h _ hh hab]
      rfl)
    (by
      intro j hj
      have hj' : j < h := by simpa only [mapTensor, hcols] using hj
      have hbb := row_major_bound h n j (t%n) hj' (Nat.mod_lt t hn)
      simp [mapTensor, inputMatrix, hbb])

def hiddenValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  hiddenValueWith ops input 256 1024 t

def outputValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  outputValueWith ops input 256 1024 256 t

theorem hidden_cell (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 65536) :
    (hiddenTensor ops input).cell t = some (hiddenValue ops input t) :=
  hiddenWith_cell ops input 64 256 1024 t (by decide) ht

theorem reference_cell (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 16384) :
    (referenceTensor ops input).cell t = some (outputValue ops input t) :=
  referenceWith_cell ops input 64 256 1024 256 t (by decide) (by decide) ht

theorem reference_outside (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : 16384 ≤ t) :
    (referenceTensor ops input).cell t = none := by
  change ops.toHalf <$> (if t < 16384 then _ else none) = none
  simp [Nat.not_lt.mpr ht]

theorem mapM_cells (indices : List Nat) (cell : Nat → Option α) (value : Nat → α)
    (hc : ∀ i ∈ indices, cell i = some (value i)) :
    indices.mapM cell = some (indices.map value) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      have hi := hc i (by simp)
      have hr := ih (fun j hj => hc j (by simp [hj]))
      simp [List.mapM_cons, hi, hr]

def extractReference (ops : Ops α) (input : Nat → Nat → α)
    (body : TensorReference) : Option (List α) := do
  let tensor ← evaluate ops input body
  if tensor.rows = 64 ∧ tensor.columns = 256 then
    (List.range 16384).mapM tensor.cell else none

def referenceSpec (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range 16384).map (outputValue ops input)

theorem extract_evaluated_tensor (ops : Ops α) (input : Nat → Nat → α) (body : TensorReference)
    (tensor : Tensor α) (values : Nat → α)
    (he : evaluate ops input body = some tensor) (hs : tensor.rows = 64 ∧ tensor.columns = 256)
    (hc : ∀ i, i < 16384 → tensor.cell i = some (values i)) :
    extractReference ops input body = some ((List.range 16384).map values) := by
  unfold extractReference
  rw [he]
  change (if tensor.rows = 64 ∧ tensor.columns = 256 then
    (List.range 16384).mapM tensor.cell else none) = _
  rw [if_pos hs]
  exact mapM_cells (List.range 16384) _ _ (fun i hi => hc i (List.mem_range.mp hi))

theorem extract_reference_body (ops : Ops α) (input : Nat → Nat → α) :
    extractReference ops input referenceBody = some (referenceSpec ops input) :=
  extract_evaluated_tensor ops input referenceBody (referenceTensor ops input) (outputValue ops input)
    (evaluate_body ops input) (reference_shape ops input) (reference_cell ops input)

#print axioms evaluate_up
#print axioms multiply_cell
#print axioms evaluate_body
#print axioms hidden_shape
#print axioms reference_shape
#print axioms hiddenWith_shape
#print axioms dot_fold
#print axioms multiply_fold
#print axioms mapped_multiply_fold
#print axioms double_mapped_multiply_fold
#print axioms row_major_bound
#print axioms hiddenWith_cell
#print axioms referenceWith_cell
#print axioms hidden_cell
#print axioms reference_cell
#print axioms reference_outside
#print axioms mapM_cells
#print axioms extract_evaluated_tensor
#print axioms extract_reference_body
end LarkPtxFeedForward.Reference
