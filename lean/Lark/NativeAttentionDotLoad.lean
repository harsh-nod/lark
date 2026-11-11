import Lark.NativeAttentionComputeReady

/-! Actual shared Q/K loads for the source's 256-component score dot product. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setReg)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def tileIndex (row col : Nat) : Index := .add (.mul (.ivar row) (.const 256)) (.ivar col)
def qValue (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat) : α :=
  ops.fromHalf (input 1 (globalAddress t tile col))
def kValue (ops : Ops α) (input : Nat → Nat → α) (t tile row col : Nat) : α :=
  ops.fromHalf (input 2 (tileAddress t tile row col))

theorem query_read_code : program[34]? = some (.assign 2 (.load .shared 0 (sharedIndex 10))) := rfl
theorem key_read_code : program[35]? = some (.assign 3 (.load .shared 1 (tileIndex 9 10))) := rfl

theorem eval_tile_index (g : Geometry) (t rowReg colReg row col : Nat) (s : State α)
    (hr : row < 32) (hc : col < 256) (hrow : s.indices t rowReg = some (row : Int))
    (hcol : s.indices t colReg = some (col : Int)) :
    evalIndex g t s (tileIndex rowReg colReg) = some ((row * 256 + col : Nat) : Int) := by
  have hm := LarkMatrix.eval_mul_nat g t s (.ivar rowReg) (.const 256) row 256 hrow (by rfl) (by omega)
  exact LarkMatrix.eval_add_nat g t s (.mul (.ivar rowReg) (.const 256)) (.ivar colReg)
    (row * 256) col hm hcol (by omega)

theorem eval_load_of (ops : Ops α) (l : Layout) (g : Geometry) (t b : Nat) (space : Space)
    (ix : Index) (s : State α) (index : Int) (cell : Location) (v : α)
    (hi : evalIndex g t s ix = some index) (hl : location l g t space b index false = some cell)
    (hv : s.memory cell = some v) : evalExpr ops l g t (.load space b ix) s = some (v, record s t cell false) := by
  simp only [evalExpr, hi, hl, hv, bind, pure, Option.bind]

theorem execute_assign_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s evaluated : State α) (v : α) (he : evalExpr ops l g t e s = some (v, evaluated))
    (hp : s.pc t + 1 = pc) : execute ops l g t (.assign r e) s = some (setReg evaluated t r v pc) := by
  simp only [execute, he, hp, bind, pure, Option.bind]
  rfl

theorem load_query (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile col : Nat) (s : State α) (hc : col < 256) (hq : QiReady ops input t tile s)
    (hlane : s.indices t 1 = some ((t % 32 : Nat) : Int)) (hcol : s.indices t 10 = some (col : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .shared 0 (sharedIndex 10)) s =
      some (qValue ops input t tile col, record s t (sharedCell t 0 (sharedAddress t col)) false) :=
  eval_load_of ops (layout p) (geometry p) t 0 .shared (sharedIndex 10) s (sharedAddress t col) _ _
    (eval_shared_index (geometry p) t 10 col s hc hlane hcol)
    (shared_location p t 0 _ false (by decide) (shared_address_bound t col hc)) (hq col hc)

theorem load_key (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t tile row col : Nat) (s : State α) (hr : row < 32) (hc : col < 256)
    (hk : Tiles ops input t tile s) (hrow : s.indices t 9 = some (row : Int))
    (hcol : s.indices t 10 = some (col : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .shared 1 (tileIndex 9 10)) s =
      some (kValue ops input t tile row col, record s t (sharedCell t 1 (row * 256 + col)) false) :=
  eval_load_of ops (layout p) (geometry p) t 1 .shared (tileIndex 9 10) s ((row * 256 + col : Nat) : Int) _ _
    (eval_tile_index (geometry p) t 9 10 row col s hr hc hrow hcol)
    (shared_location p t 1 (row * 256 + col) false (by decide) (by omega)) (hk 1 (Or.inl rfl) row hr col hc)

theorem record_good (s : State α) (t : Nat) (l : Location) (write : Bool)
    (hg : TraceGood s) (ha : Good ⟨t, l, write, s.epochs t⟩) : TraceGood (record s t l write) := by
  intro a hm
  rcases List.mem_cons.mp hm with he | hm
  · exact he ▸ ha
  · exact hg a hm

theorem key_read_good (t row col : Nat) (epoch : Epoch) (he : epoch.block % 2 = 1) :
    Good ⟨t, sharedCell t 1 (row * 256 + col), false, epoch⟩ :=
  Good.tileLoad rfl rfl (Or.inl rfl) he rfl

#print axioms load_query
#print axioms load_key
#print axioms key_read_good
end LarkNativeAttention
