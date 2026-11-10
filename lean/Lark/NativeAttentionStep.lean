import Lark.NativeAttentionEval

/-! Small instruction lemmas over arbitrary states keep execution proofs modular. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem execute_store_of (ops : Ops α) (l : Layout) (g : Geometry) (t pc : Nat)
    (space : Space) (buffer : Nat) (ix : Index) (e : Expr) (s evaluated : State α)
    (index : Int) (cell : Location) (value : α)
    (hi : evalIndex g t s ix = some index)
    (hl : location l g t space buffer index true = some cell)
    (he : evalExpr ops l g t e s = some (value, evaluated))
    (hp : s.pc t + 1 = pc) :
    execute ops l g t (.store space buffer ix e) s =
      some (storeState evaluated t cell value pc) := by
  simp only [execute, hi, hl, he, hp, bind, pure, Option.bind]
  rfl

theorem execute_branch_of (ops : Ops α) (l : Layout) (g : Geometry) (t pc target : Nat)
    (pred : Predicate) (s : State α) (value : Bool)
    (he : evalPredicate g t s pred = some value) (hp : s.pc t + 1 = pc) :
    execute ops l g t (.branch pred target) s =
      some (advance s t (if value then pc else target)) := by
  simp only [execute, he, hp, bind, pure, Option.bind]

theorem zero_store_eq (p : Shape) (ops : Ops α) (t tile col : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hn : NativeIndices t s) (hrow : s.indices t 3 = some (tile : Int))
    (hcol : s.indices t 4 = some (col : Int)) (hp : s.pc t = 7) :
    execute ops (layout p) (geometry p) t
      (.store .global 0 initIndex (.un .toHalf (.lit 0 1))) s =
      some (storeState s t (globalCell 0 (globalAddress t tile col))
        (ops.toHalf (ops.literal 0 1)) 8) := by
  exact execute_store_of ops (layout p) (geometry p) t 8 .global 0 initIndex
    (.un .toHalf (.lit 0 1)) s s (globalAddress t tile col) _ _
    (eval_init_index p t tile col s ht hi hc hn hrow hcol)
    (output_location p t _ true (global_address_bound p t tile col ht hi hc))
    (by rfl) (by omega)

#print axioms zero_store_eq
end LarkNativeAttention
