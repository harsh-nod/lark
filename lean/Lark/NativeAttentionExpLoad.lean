import Lark.NativeAttentionScoresReady

/-! The source's recorded score load, subtraction and exponential expression. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def normalizedWeight (ops : Ops α) (score maximum : α) : α := ops.exp (ops.sub score maximum)

theorem exp_assign_code : program[51]? = some (.assign 6
    (.un .exp (.bin .sub (.load .shared 3 (scoreIndex 11)) (.reg 0)))) := rfl
theorem exp_store_code : program[52]? = some (.store .shared 3 (scoreIndex 11) (.reg 6)) := rfl

theorem eval_unary_of (ops : Ops α) (l : Layout) (g : Geometry) (t : Nat) (op : Unary) (e : Expr)
    (s next : State α) (v : α) (he : evalExpr ops l g t e s = some (v, next)) :
    evalExpr ops l g t (.un op e) s = some (applyUnary ops op v, next) := by
  simp only [evalExpr, he, bind, pure, Option.bind]

theorem load_score (p : Shape) (ops : Ops α) (t reg col : Nat) (value : α) (s : State α)
    (hc : col < 32) (hlane : s.indices t 1 = some ((t % 32 : Nat) : Int))
    (hcol : s.indices t reg = some (col : Int)) (hv : s.memory (sharedCell t 3 (scoreAddress t col)) = some value) :
    evalExpr ops (layout p) (geometry p) t (.load .shared 3 (scoreIndex reg)) s =
      some (value, record s t (sharedCell t 3 (scoreAddress t col)) false) :=
  eval_load_of ops (layout p) (geometry p) t 3 .shared (scoreIndex reg) s (scoreAddress t col) _ value
    (eval_score_index (geometry p) t reg col s hc hlane hcol)
    (score_location p t _ false (score_address_bound t col hc)) hv

theorem eval_normalized_weight (p : Shape) (ops : Ops α) (t col : Nat) (score maximum : α) (s : State α)
    (hc : col < 32) (hlane : s.indices t 1 = some ((t % 32 : Nat) : Int))
    (hcol : s.indices t 11 = some (col : Int)) (hm : s.regs t 0 = some maximum)
    (hv : s.memory (sharedCell t 3 (scoreAddress t col)) = some score) :
    evalExpr ops (layout p) (geometry p) t
      (.un .exp (.bin .sub (.load .shared 3 (scoreIndex 11)) (.reg 0))) s =
      some (normalizedWeight ops score maximum, record s t (sharedCell t 3 (scoreAddress t col)) false) := by
  have hload := load_score p ops t 11 col score s hc hlane hcol hv
  have hm' : evalExpr ops (layout p) (geometry p) t (.reg 0)
      (record s t (sharedCell t 3 (scoreAddress t col)) false) =
      some (maximum, record s t (sharedCell t 3 (scoreAddress t col)) false) := by
    simp [evalExpr, record, hm]
  have hsub := LarkReduction.eval_bin_of ops (layout p) (geometry p) t .sub
    (.load .shared 3 (scoreIndex 11)) (.reg 0) s _ _ score maximum hload hm'
  exact eval_unary_of ops (layout p) (geometry p) t .exp _ s _ _ hsub

#print axioms load_score
#print axioms eval_normalized_weight
end LarkNativeAttention
