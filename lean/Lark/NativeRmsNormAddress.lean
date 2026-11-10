import Lark.NativeRmsNormInit

/-! Actual index evaluation and FP16 input loads for both native vector loops.
No execution or race-freedom premise is assumed in the initial-read theorem.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (int32_cast eval_mul_of eval_add_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def globalCell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩
def scalarAddress (row vector component : Nat) : Nat := row * 16384 + vector * 8 + component

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i < p.rows * 16384 → s.memory (globalCell 1 i) = some (input 1 i)) ∧
  (∀ i, i < 16384 → s.memory (globalCell 2 i) = some (input 2 i))

theorem initial_reads (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (initial (layout p) input outside) := by
  constructor
  · intro i hi
    exact initial_places _ _ _ 1 i ⟨.input, p.rows * 16384⟩ rfl rfl hi
  · intro i hi
    exact initial_places _ _ _ 2 i ⟨.input, 16384⟩ rfl rfl hi

theorem reads_of_memory (p : Shape) (input : Nat → Nat → α) (s u : State α)
    (hr : Reads p input s) (hm : u.memory = s.memory) : Reads p input u := by
  simpa only [Reads, hm] using hr

theorem vector_column_bound (vector component : Nat) (hv : vector < 2048) (hc : component < 8) :
    vector * 8 + component < 16384 := by omega

theorem scalar_address_bound (p : Shape) (row vector component : Nat)
    (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8) :
    scalarAddress row vector component < p.rows * 16384 := by
  have h := LarkReduction.address_bound p.rows 16384 row (vector * 8 + component)
    hr (vector_column_bound vector component hv hc)
  simpa only [scalarAddress, Nat.add_assoc] using h

theorem eval_nat_product (g : Geometry) (t reg value factor : Nat) (s : State α)
    (hi : s.indices t reg = some (value : Int)) (hf : factor < 2147483648)
    (hp : value * factor < 2147483648) :
    evalIndex g t s (.mul (.ivar reg) (.const (factor : Int))) = some ((value * factor : Nat) : Int) := by
  exact eval_mul_of g t s _ _ (value : Int) (factor : Int) _ hi (int32_cast factor hf)
    ((congrArg int32 (Int.natCast_mul value factor).symm).trans (int32_cast _ hp))

theorem eval_nat_sum (g : Geometry) (t x y : Nat) (s : State α) (a b : Index)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hs : x + y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x + y : Nat) : Int) := by
  exact eval_add_of g t s a b (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_add x y).symm).trans (int32_cast _ hs))

theorem eval_column (g : Geometry) (t vr cr vector component : Nat) (s : State α)
    (hi : s.indices t vr = some (vector : Int)) (hj : s.indices t cr = some (component : Int))
    (hv : vector < 2048) (hc : component < 8) :
    evalIndex g t s (columnIndex vr cr) = some ((vector * 8 + component : Nat) : Int) := by
  have hm := eval_nat_product g t vr vector 8 s hi (by decide) (by omega)
  exact eval_nat_sum g t (vector * 8) component s _ _ hm hj (by omega)

theorem eval_row_address (p : Shape) (g : Geometry) (t vr cr row vector component : Nat) (s : State α)
    (hi : s.indices t 0 = some (row : Int))
    (hvIndex : s.indices t vr = some (vector : Int)) (hcIndex : s.indices t cr = some (component : Int))
    (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8) :
    evalIndex g t s (rowIndex vr cr) = some ((scalarAddress row vector component : Nat) : Int) := by
  have hp := p.bound
  have hrow := eval_nat_product g t 0 row 16384 s hi (by decide) (by omega)
  have hvec := eval_nat_product g t vr vector 8 s hvIndex (by decide) (by omega)
  have hpartial := eval_nat_sum g t (row * 16384) (vector * 8) s _ _ hrow hvec (by omega)
  exact eval_nat_sum g t (row * 16384 + vector * 8) component s _ _ hpartial hcIndex (by omega)

theorem load_input (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t vr cr row vector component : Nat) (s : State α) (reads : Reads p input s)
    (hi : s.indices t 0 = some (row : Int))
    (hvIndex : s.indices t vr = some (vector : Int)) (hcIndex : s.indices t cr = some (component : Int))
    (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (rowIndex vr cr))) s =
      some (ops.fromHalf (input 1 (scalarAddress row vector component)),
        record s t (globalCell 1 (scalarAddress row vector component)) false) := by
  have he := eval_row_address p (geometry p) t vr cr row vector component s hi hvIndex hcIndex hr hv hc
  have hb := scalar_address_bound p row vector component hr hv hc
  have hneg : ¬ ((scalarAddress row vector component : Nat) : Int) < 0 := by omega
  have hl : location (layout p) (geometry p) t .global 1
      ((scalarAddress row vector component : Nat) : Int) false =
        some (globalCell 1 (scalarAddress row vector component)) := by
    simp [location, layout, globalCell, hneg, hb]
  simp only [evalExpr, he, hl, reads.1 _ hb, applyUnary, bind, pure, Option.bind]

theorem load_weight (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t vr cr vector component : Nat) (s : State α) (reads : Reads p input s)
    (hvIndex : s.indices t vr = some (vector : Int)) (hcIndex : s.indices t cr = some (component : Int))
    (hv : vector < 2048) (hc : component < 8) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 2 (columnIndex vr cr))) s =
      some (ops.fromHalf (input 2 (vector * 8 + component)),
        record s t (globalCell 2 (vector * 8 + component)) false) := by
  have he := eval_column (geometry p) t vr cr vector component s hvIndex hcIndex hv hc
  have hb := vector_column_bound vector component hv hc
  have hl : location (layout p) (geometry p) t .global 2
      ((vector * 8 + component : Nat) : Int) false = some (globalCell 2 (vector * 8 + component)) := by
    have all : ∀ i : Nat, i < 16384 →
        location (layout p) (geometry p) t .global 2 (i : Int) false = some (globalCell 2 i) := by
      intro i hi
      simp [location, layout, globalCell, hi]
    exact all _ hb
  simp only [evalExpr, he, hl, reads.2 _ hb, applyUnary, bind, pure, Option.bind]

theorem input_access_good (p : Shape) (s : State α) (t buffer offset : Nat) (hb : buffer ≠ 0) :
    LarkReductionFootprint.Good (traversal p) 0 ⟨t, globalCell buffer offset, false, s.epochs t⟩ :=
  .input rfl rfl hb rfl

#print axioms initial_reads
#print axioms eval_row_address
#print axioms load_input
#print axioms load_weight
#print axioms input_access_good
end LarkNativeRmsNorm
