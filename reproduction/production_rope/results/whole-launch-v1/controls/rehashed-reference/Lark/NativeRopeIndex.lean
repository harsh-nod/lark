import Lark.NativeRopeState
import Lark.Reduction

/-! Checked integer operations and gathered-cache loads used by both native
loop headers. Every source arithmetic operation retains its int32 guard. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev setIndex := @LarkReduction.setIndex

theorem eval_nat_mul (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hxy : x * y < 2147483648) :
    evalIndex g t s (.mul a b) = some ((x * y : Nat) : Int) := by
  exact LarkReduction.eval_mul_of g t s a b (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_mul x y).symm).trans (LarkReduction.int32_cast _ hxy))

theorem eval_nat_add (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Nat)
    (ha : evalIndex g t s a = some (x : Int)) (hb : evalIndex g t s b = some (y : Int))
    (hxy : x + y < 2147483648) :
    evalIndex g t s (.add a b) = some ((x + y : Nat) : Int) := by
  exact LarkReduction.eval_add_of g t s a b (x : Int) (y : Int) _ ha hb
    ((congrArg int32 (Int.natCast_add x y).symm).trans (LarkReduction.int32_cast _ hxy))

theorem eval_head (g : Geometry) (t r pair : Nat) (s : State α)
    (hr : s.indices t r = some (pair : Int)) :
    evalIndex g t s (.div (.ivar r) (.const 64)) = some ((pair / 64 : Nat) : Int) := by
  have hn : ¬ (pair : Int) < 0 := by omega
  simp [evalIndex, hr, int32, hn] <;> omega

theorem eval_pair_remainder (g : Geometry) (t r pair : Nat) (s : State α)
    (hr : s.indices t r = some (pair : Int)) :
    evalIndex g t s (.mod (.ivar r) (.const 64)) = some ((pair % 64 : Nat) : Int) := by
  have hn : ¬ (pair : Int) < 0 := by omega
  simp [evalIndex, hr, int32, hn] <;> omega

theorem eval_cache_cos_address (p : Shape) (g : Geometry) (t row remainder rr jr : Nat)
    (s : State α) (hr : row < p.rows) (hj : remainder < 64)
    (hrow : s.indices t rr = some (row : Int)) (hrem : s.indices t jr = some (remainder : Int)) :
    evalIndex g t s (.add (.mul (.ivar rr) (.const 128)) (.ivar jr)) =
      some ((row * 128 + remainder : Nat) : Int) := by
  have hs := p.bound
  have hm := eval_nat_mul g t s (.ivar rr) (.const 128) row 128 hrow
    (by rfl) (by omega)
  exact eval_nat_add g t s _ _ (row * 128) remainder hm hrem (by omega)

theorem cache_location (p : Shape) (t offset : Nat) (hi : offset < p.rows * 128) :
    location (layout p) (geometry p) t .global 2 (offset : Int) false =
      some (globalCell 2 offset) := by
  simp [location, layout, globalCell, hi]

theorem load_cache (p : Shape) (ops : Ops α) (t offset index : Nat) (s : State α) (value : α)
    (hi : offset < p.rows * 128) (hindex : s.indices t index = some (offset : Int))
    (hm : s.memory (globalCell 2 offset) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 2 (.ivar index))) s =
      some (ops.fromHalf value, record s t (globalCell 2 offset) false) := by
  simp only [evalExpr, evalIndex, hindex, cache_location p t offset hi,
    hm, applyUnary, bind, pure, Option.bind]

theorem cache_access_good (neox : Bool) (t offset : Nat) (epoch : Epoch) :
    Good neox ⟨t, globalCell 2 offset, false, epoch⟩ := .cache rfl rfl rfl rfl

#print axioms eval_nat_mul
#print axioms eval_nat_add
#print axioms eval_head
#print axioms eval_pair_remainder
#print axioms eval_cache_cos_address
#print axioms cache_location
#print axioms load_cache
#print axioms cache_access_good
end LarkNativeRope
