import Lark.NativeQKNormRopeLoads

/-! Exact source-order square-and-accumulate pairs before the first shuffle. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def InputValues (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop :=
  ∀ e, e < 4 → s.regs t e = some (inputValue ops input t e)

def squarePrefix (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : Nat → α
  | 0 => ops.literal 0 1
  | e + 1 => ops.add (squarePrefix ops input t e)
      (ops.mul (inputValue ops input t e) (inputValue ops input t e))

def squareAt (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) : State α :=
  let s := setReg s t (5 + e)
    (ops.mul (inputValue ops input t e) (inputValue ops input t e)) (17 + 2 * e)
  setReg s t 4 (squarePrefix ops input t (e + 1)) (18 + 2 * e)

theorem square_at_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t e extra : Nat) (s : State α) (he : e < 4) (hp : s.pc t = 16 + 2 * e)
    (hv : InputValues ops input t s) (ha : s.regs t 4 = some (squarePrefix ops input t e)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (squareAt ops input t e s) := by
  let value := inputValue ops input t e
  let s1 := setReg s t (5 + e) (ops.mul value value) (17 + 2 * e)
  let s2 := setReg s1 t 4 (squarePrefix ops input t (e + 1)) (18 + 2 * e)
  have e1 := execute_pure_of ops (layout p) (geometry p) t (5 + e) (17 + 2 * e)
    (.bin .mul (.reg e) (.reg e)) s (ops.mul value value)
    (by simp [evalExpr, hv e he, applyBinary, value]) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have hne : ¬ (4 : Nat) = 5 + e := by omega
  have hacc : s1.regs t 4 = some (squarePrefix ops input t e) := by
    simpa [s1, setReg, advance, hne] using ha
  have hsq : s1.regs t (5 + e) = some (ops.mul value value) := by simp [s1, setReg, advance]
  have e2 := execute_pure_of ops (layout p) (geometry p) t 4 (18 + 2 * e)
    (.bin .add (.reg 4) (.reg (5 + e))) s1 (squarePrefix ops input t (e + 1))
    (by simp [evalExpr, hacc, hsq, applyBinary, squarePrefix, value])
    (by simp [s1, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have code1 : (program neox)[16 + 2 * e]? =
      some (.scalar (.assign (5 + e) (.bin .mul (.reg e) (.reg e)))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  have code2 : (program neox)[17 + 2 * e]? =
      some (.scalar (.assign 4 (.bin .add (.reg 4) (.reg (5 + e))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  rewrite [scalar_step p neox ops t (16 + 2 * e) (extra + 1) _ s s1 code1 hp e1]
  rewrite [scalar_step p neox ops t (17 + 2 * e) extra _ s1 s2 code2
    (by simp [s1, setReg, advance]) e2]
  rfl

theorem square_at_pc (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (squareAt ops input t e s).pc t = 18 + 2 * e := by simp [squareAt, setReg, advance]

theorem square_at_acc (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (squareAt ops input t e s).regs t 4 = some (squarePrefix ops input t (e + 1)) := by
  simp [squareAt, setReg, advance]

theorem square_at_reg (ops : Ops α) (input : Nat → Nat → α) (t e r : Nat)
    (s : State α) (hr : r < 4) : (squareAt ops input t e s).regs t r = s.regs t r := by
  have h4 : ¬ r = 4 := by omega
  have he : ¬ r = 5 + e := by omega
  simp [squareAt, setReg, advance, h4, he]

theorem square_at_values (ops : Ops α) (input : Nat → Nat → α) (t e : Nat)
    (s : State α) (hv : InputValues ops input t s) : InputValues ops input t (squareAt ops input t e s) := by
  intro r hr
  rw [square_at_reg ops input t e r s hr]
  exact hv r hr

theorem square_at_preserves (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) (s : State α) :
    (squareAt ops input t e s).memory = s.memory ∧ (squareAt ops input t e s).trace = s.trace ∧
    (squareAt ops input t e s).epochs = s.epochs ∧ (squareAt ops input t e s).indices = s.indices :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms square_at_eq
#print axioms square_at_pc
#print axioms square_at_acc
#print axioms square_at_reg
#print axioms square_at_values
#print axioms square_at_preserves
end LarkNativeQKNormRope
