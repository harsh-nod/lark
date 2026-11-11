import Lark.NativeRopeIndex

/-! Source index expressions for both rotary pair layouts and both Q/K row
strides. Overflow and division guards are discharged in the pinned machine. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def component (neox : Bool) (pair : Nat) (imaginary : Bool) : Nat :=
  if neox then pair % 64 + (if imaginary then 64 else 0)
  else 2 * (pair % 64) + (if imaginary then 1 else 0)
def xIndex (neox : Bool) (reg : Nat) : Index :=
  if neox then .ivar reg else .mul (.const 2) (.ivar reg)
def yIndex (neox : Bool) (reg : Nat) : Index :=
  if neox then .add (.ivar reg) (.const 64)
  else .add (.mul (.const 2) (.ivar reg)) (.const 1)
def cacheCos (row pair : Nat) : Nat := row * 128 + pair % 64
def cacheSin (row pair : Nat) : Nat := cacheCos row pair + 64

theorem component_bound (neox imaginary : Bool) (pair : Nat) : component neox pair imaginary < 128 := by
  have h := Nat.mod_lt pair (by decide : 0 < 64)
  cases neox <;> cases imaginary <;> simp [component] <;> omega

theorem pair_column_component (neox imaginary : Bool) (pair : Nat) :
    pairColumn neox pair imaginary = pair / 64 * 128 + component neox pair imaginary := by
  cases neox <;> cases imaginary <;> simp [pairColumn, component] <;> omega

theorem eval_x (g : Geometry) (t reg pair : Nat) (s : State α) (neox : Bool)
    (hr : s.indices t reg = some ((pair % 64 : Nat) : Int)) :
    evalIndex g t s (xIndex neox reg) = some ((component neox pair false : Nat) : Int) := by
  have hj := Nat.mod_lt pair (by decide : 0 < 64)
  cases neox
  · simpa [xIndex, component] using eval_nat_mul g t s (.const 2) (.ivar reg)
      2 (pair % 64) (by rfl) hr (by omega)
  · simpa [xIndex, component] using hr

theorem eval_y (g : Geometry) (t reg pair : Nat) (s : State α) (neox : Bool)
    (hr : s.indices t reg = some ((pair % 64 : Nat) : Int)) :
    evalIndex g t s (yIndex neox reg) = some ((component neox pair true : Nat) : Int) := by
  have hj := Nat.mod_lt pair (by decide : 0 < 64)
  cases neox
  · have hm := eval_nat_mul g t s (.const 2) (.ivar reg) 2 (pair % 64) (by rfl) hr (by omega)
    simpa [yIndex, component] using eval_nat_add g t s _ (.const 1) (2 * (pair % 64)) 1 hm (by rfl) (by omega)
  · simpa [yIndex, component] using eval_nat_add g t s (.ivar reg) (.const 64) (pair % 64) 64 hr (by rfl) (by omega)

theorem cache_bounds (p : Shape) (row pair : Nat) (hr : row < p.rows) :
    cacheCos row pair < p.rows * 128 ∧ cacheSin row pair < p.rows * 128 := by
  have hj := Nat.mod_lt pair (by decide : 0 < 64)
  simp only [cacheCos, cacheSin]
  omega

theorem eval_pair_address (p : Shape) (g : Geometry) (t buffer row pair rr hr cr : Nat)
    (s : State α) (neox imaginary : Bool) (hrow : row < p.rows) (hp : pair < pairs buffer)
    (hi0 : s.indices t rr = some (row : Int))
    (hi1 : s.indices t hr = some ((pair / 64 : Nat) : Int))
    (hi2 : s.indices t cr = some ((component neox pair imaginary : Nat) : Int)) :
    evalIndex g t s (.add (.add (.mul (.ivar rr) (.const (width buffer : Int)))
      (.mul (.ivar hr) (.const 128))) (.ivar cr)) =
      some ((address buffer row pair neox imaginary : Nat) : Int) := by
  have total := address_int32 p buffer row pair neox imaginary hrow hp
  rw [address, pair_column_component] at total
  have hw : width buffer < 2147483648 := by unfold width; split <;> decide
  have em0 := eval_nat_mul g t s (.ivar rr) (.const (width buffer : Int)) row (width buffer)
    hi0 (LarkReduction.int32_cast _ hw) (by omega)
  have em1 := eval_nat_mul g t s (.ivar hr) (.const 128) (pair / 64) 128 hi1 (by rfl) (by omega)
  have ea0 := eval_nat_add g t s _ _ (row * width buffer) (pair / 64 * 128) em0 em1 (by omega)
  have ea1 := eval_nat_add g t s _ (.ivar cr) (row * width buffer + pair / 64 * 128)
    (component neox pair imaginary) ea0 hi2 (by omega)
  simpa only [address, pair_column_component, Nat.add_assoc] using ea1

#print axioms component_bound
#print axioms pair_column_component
#print axioms eval_x
#print axioms eval_y
#print axioms cache_bounds
#print axioms eval_pair_address
end LarkNativeRope
