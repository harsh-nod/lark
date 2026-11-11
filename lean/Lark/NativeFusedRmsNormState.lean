import Lark.NativeFusedRmsNormAddress

/-! Scalar execution helpers for the fixed native in-place program. The pinned
machine is unchanged; stores retain both their actual memory effect and trace.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast eval_mul_of eval_add_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def globalCell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩
def unroundedCell (t col : Nat) : Location := ⟨.shared, t / 1024, 1, col⟩

def written (t pc : Nat) (loc : Location) (value : α) (s : State α) : State α :=
  advance { record s t loc true with
    memory := fun l => if l = loc then some value else s.memory l } t pc

theorem written_memory (t pc : Nat) (loc l : Location) (value : α) (s : State α) :
    (written t pc loc value s).memory l = if l = loc then some value else s.memory l := rfl

theorem written_other (t pc : Nat) (loc l : Location) (value : α) (s : State α)
    (hl : l ≠ loc) : (written t pc loc value s).memory l = s.memory l := by
  simp only [written_memory, if_neg hl]

theorem scalar_step (p : Shape) (ops : Ops α) (t pc extra : Nat)
    (i : LarkNonlinear.Instr) (s next : State α)
    (hi : program[pc]? = some (.scalar i)) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra next := by
  have parked : LarkCollective.parked program s t = none := by
    cases i <;> simp_all [LarkCollective.parked, execute]
  rewrite [LarkCollective.runLane, parked]
  simp only [hp, hi, bind, pure, Option.bind, he]

theorem eval_nat_mul (g : Geometry) (t value factor : Nat) (s : State α) (a : Index)
    (ha : evalIndex g t s a = some (value : Int))
    (hf : factor < 2147483648) (hp : value * factor < 2147483648) :
    evalIndex g t s (.mul a (.const (factor : Int))) = some ((value * factor : Nat) : Int) :=
  eval_mul_of g t s _ _ (value : Int) (factor : Int) _ ha (int32_cast factor hf)
    ((congrArg int32 (Int.natCast_mul value factor).symm).trans (int32_cast _ hp))

theorem eval_nat_sum (g : Geometry) (t x y : Nat) (s : State α) (a b : Index)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hs : x + y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x + y : Nat) : Int) :=
  eval_add_of g t s _ _ (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_add x y).symm).trans (int32_cast _ hs))

def columnIndex (iteration component : Nat) : Index :=
  .add (.mul (.add (.mul (.ivar iteration) (.const 1024)) (.ivar 1)) (.const 8))
    (.ivar component)

theorem eval_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h1 : s.indices t 1 = some (tid : Int))
    (h4 : s.indices t 4 = some (iteration : Int)) (h5 : s.indices t 5 = some (component : Int)) :
    evalIndex (geometry p) t s (columnIndex 4 5) = some ((column tid iteration component : Nat) : Int) := by
  have hmul := eval_nat_mul (geometry p) t iteration 1024 s (.ivar 4) h4 (by decide) (by omega)
  have hadd := eval_nat_sum (geometry p) t (iteration * 1024) tid s _ (.ivar 1) hmul h1 (by omega)
  have hvec := eval_nat_mul (geometry p) t (iteration * 1024 + tid) 8 s _ hadd (by decide) (by omega)
  exact eval_nat_sum (geometry p) t ((iteration * 1024 + tid) * 8) component s _ _ hvec h5 (by omega)

theorem eval_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row < p.rows) (hc : col < 16384)
    (h0 : s.indices t 0 = some (row : Int)) (h6 : s.indices t 6 = some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 16384)) (.ivar 6)) =
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hmul := eval_nat_mul (geometry p) t row 16384 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row * 16384) col s _ _ hmul h6 (by omega)

theorem mutable_location (p : Shape) (t buffer offset : Nat) (write : Bool)
    (hb : buffer = 0 ∨ buffer = 1) (hi : offset < p.rows * 16384) :
    location (layout p) (geometry p) t .global buffer (offset : Int) write =
      some (globalCell buffer offset) := by
  rcases hb with rfl | rfl <;>
    cases write <;> simp [location, layout, globalCell, hi,
      show (Role.output == Role.input) = false from rfl]

theorem unrounded_location (p : Shape) (t col : Nat) (write : Bool) (hc : col < 16384) :
    location (layout p) (geometry p) t .shared 1 (col : Int) write = some (unroundedCell t col) := by
  simp [location, layout, geometry, unroundedCell, hc]

#print axioms scalar_step
#print axioms eval_column
#print axioms eval_address
#print axioms mutable_location
#print axioms unrounded_location
end LarkNativeFusedRmsNorm
