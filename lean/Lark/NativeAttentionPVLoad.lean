import Lark.NativeAttentionOutputPrepare

/-! Actual source loads for the exponential-weight by V dot products. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def vValue (ops : Ops α) (input : Nat → Nat → α) (t key row col : Nat) : α :=
  ops.fromHalf (input 3 (tileAddress t key row col))

theorem pv_weight_read_code : program[70]? = some (.assign 14 (.load .shared 3 (scoreIndex 13))) := rfl
theorem pv_value_read_code : program[71]? = some (.assign 15 (.load .shared 2 (tileIndex 13 12))) := rfl

theorem load_weight (p : Shape) (ops : Ops α) (t row : Nat) (weights : Nat → α) (s : State α)
    (hr : row < 32) (hw : ScoreRange t weights 0 32 s) (hn : NativeIndices t s)
    (hrow : s.indices t 13 = some (row : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .shared 3 (scoreIndex 13)) s =
      some (weights row, record s t (sharedCell t 3 (scoreAddress t row)) false) :=
  load_score p ops t 13 row (weights row) s hr hn.2.1 hrow (hw row (by omega) hr)

theorem load_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t key row col : Nat) (s : State α) (hr : row < 32) (hc : col < 256)
    (hk : Tiles ops input t key s) (hrow : s.indices t 13 = some (row : Int))
    (hcol : s.indices t 12 = some (col : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .shared 2 (tileIndex 13 12)) s =
      some (vValue ops input t key row col, record s t (sharedCell t 2 (row * 256 + col)) false) :=
  eval_load_of ops (layout p) (geometry p) t 2 .shared (tileIndex 13 12) s ((row * 256 + col : Nat) : Int) _ _
    (eval_tile_index (geometry p) t 13 12 row col s hr hc hrow hcol)
    (shared_location p t 2 (row * 256 + col) false (by decide) (by omega)) (hk 2 (Or.inr rfl) row hr col hc)

theorem value_read_good (t row col : Nat) (epoch : Epoch) (he : epoch.block % 2 = 1) :
    Good ⟨t, sharedCell t 2 (row * 256 + col), false, epoch⟩ := Good.tileLoad rfl rfl (Or.inr rfl) he rfl

#print axioms load_weight
#print axioms load_value
end LarkNativeAttention
