import Lark.NativeQKNormRopeState

/-! Evaluation of the native header's actual checked index expressions. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem eval_head_global (p : Shape) (t : Nat) (s : State α) (ht : t < p.rows * 1280) :
    evalIndex (geometry p) t s (.add (.mul .bid (.const 8)) (.div .tid (.const 32))) =
      some ((t / 32 : Nat) : Int) := by
  have hp := p.bound
  have hm := Nat.mod_lt t (by decide : 0 < 256)
  have hbid : evalIndex (geometry p) t s .bid = some ((t / 256 : Nat) : Int) := by
    simpa only [evalIndex, geometry] using int32_cast (t / 256) (by omega)
  have htid : evalIndex (geometry p) t s .tid = some ((t % 256 : Nat) : Int) := by
    simpa only [evalIndex, geometry] using int32_cast (t % 256) (by omega)
  have hdiv := eval_nat_div_of (geometry p) t s .tid (t % 256) 32 htid (by decide) (by decide)
  have em := eval_nat_mul (geometry p) t s .bid (.const 8) (t / 256) 8 hbid rfl (by omega)
  have ea := eval_nat_add (geometry p) t s _ _ (t / 256 * 8) (t % 256 / 32) em hdiv (by omega)
  simpa only [native_head] using ea

theorem eval_row (p : Shape) (t : Nat) (s : State α)
    (h0 : s.indices t 0 = some ((t / 32 : Nat) : Int)) :
    evalIndex (geometry p) t s (.div (.ivar 0) (.const 40)) = some ((row t : Nat) : Int) := by
  simpa only [native_row] using eval_nat_div (geometry p) t 0 (t / 32) 40 s h0 (by decide) (by decide)

theorem eval_head (p : Shape) (t : Nat) (s : State α)
    (h0 : s.indices t 0 = some ((t / 32 : Nat) : Int)) :
    evalIndex (geometry p) t s (.mod (.ivar 0) (.const 40)) = some ((head t : Nat) : Int) := by
  simpa only [head] using eval_nat_mod (geometry p) t 0 (t / 32) 40 s h0 (by decide) (by decide)

theorem eval_lane (p : Shape) (t : Nat) (s : State α) :
    evalIndex (geometry p) t s (.mod .tid (.const 32)) = some ((t % 32 : Nat) : Int) := by
  have hm := Nat.mod_lt t (by decide : 0 < 256)
  have htid : evalIndex (geometry p) t s .tid = some ((t % 256 : Nat) : Int) := by
    simpa only [evalIndex, geometry] using int32_cast (t % 256) (by omega)
  have hr : t % 256 % 32 = t % 32 := by omega
  simpa only [hr] using eval_nat_mod_of (geometry p) t s .tid (t % 256) 32 htid (by decide) (by decide)

theorem eval_column (p : Shape) (t : Nat) (s : State α)
    (h3 : s.indices t 3 = some ((t % 32 : Nat) : Int)) :
    evalIndex (geometry p) t s (.mul (.ivar 3) (.const 4)) = some ((column t 0 : Nat) : Int) := by
  have hm := Nat.mod_lt t (by decide : 0 < 32)
  simpa only [column, Nat.add_zero] using
    eval_nat_mul (geometry p) t s (.ivar 3) (.const 4) (t % 32) 4 h3 rfl (by omega)

def baseIndex (stride : Nat) : Index :=
  .add (.add (.mul (.ivar 1) (.const (stride : Int))) (.mul (.ivar 2) (.const 128))) (.ivar 4)

theorem eval_base_address (p : Shape) (t stride : Nat) (s : State α)
    (ht : t < p.rows * 1280) (hw : stride ≤ 6144)
    (h1 : s.indices t 1 = some ((row t : Nat) : Int))
    (h2 : s.indices t 2 = some ((head t : Nat) : Int))
    (h4 : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    evalIndex (geometry p) t s (baseIndex stride) =
      some ((row t * stride + head t * 128 + column t 0 : Nat) : Int) := by
  have hr := row_bound p t ht
  have hh := head_bound t
  have hc := column_bound t 0 (by decide)
  have hp := p.bound
  have hm := Nat.mul_le_mul_left (row t) hw
  have hbound : row t * stride + head t * 128 + column t 0 < 2147483648 := by omega
  have er := eval_nat_mul (geometry p) t s (.ivar 1) (.const (stride : Int))
    (row t) stride h1 (int32_cast stride (by omega)) (by omega)
  have eh := eval_nat_mul (geometry p) t s (.ivar 2) (.const 128)
    (head t) 128 h2 rfl (by omega)
  have es := eval_nat_add (geometry p) t s _ _ (row t * stride) (head t * 128) er eh (by omega)
  exact eval_nat_add (geometry p) t s _ (.ivar 4) (row t * stride + head t * 128) (column t 0) es h4 hbound

theorem eval_input_base (p : Shape) (t : Nat) (s : State α)
    (ht : t < p.rows * 1280)
    (h1 : s.indices t 1 = some ((row t : Nat) : Int))
    (h2 : s.indices t 2 = some ((head t : Nat) : Int))
    (h4 : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    evalIndex (geometry p) t s (baseIndex 6144) = some ((inputAddress t 0 : Nat) : Int) :=
  eval_base_address p t 6144 s ht (by decide) h1 h2 h4

theorem eval_output_base (p : Shape) (t : Nat) (s : State α)
    (ht : t < p.rows * 1280)
    (h1 : s.indices t 1 = some ((row t : Nat) : Int))
    (h2 : s.indices t 2 = some ((head t : Nat) : Int))
    (h4 : s.indices t 4 = some ((column t 0 : Nat) : Int)) :
    evalIndex (geometry p) t s (baseIndex 5120) = some ((outputAddress t 0 : Nat) : Int) :=
  eval_base_address p t 5120 s ht (by decide) h1 h2 h4

#print axioms eval_head_global
#print axioms eval_row
#print axioms eval_head
#print axioms eval_lane
#print axioms eval_column
#print axioms eval_base_address
#print axioms eval_input_base
#print axioms eval_output_base
end LarkNativeQKNormRope
