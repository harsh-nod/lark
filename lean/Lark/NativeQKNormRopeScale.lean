import Lark.NativeQKNormRopeAdd

/-! Actual final reduction add and RMS scale computation at PCs33..36. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normalScale (ops : Ops α) (sum : α) : α :=
  ops.rsqrt (ops.add (ops.div sum (ops.literal 128 1)) (ops.literal 1 100000))

def scaleAfter (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  let sum := ops.add a b
  let mean := ops.div sum (ops.literal 128 1)
  let shifted := ops.add mean (ops.literal 1 100000)
  let s := setReg s t 4 sum 34
  let s := setReg s t 10 mean 35
  let s := setReg s t 11 shifted 36
  setReg s t 12 (ops.rsqrt shifted) 37

theorem scale_eq (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat) (a b : α)
    (s : State α) (hp : s.pc t = 33) (ha : s.regs t 4 = some a) (hb : s.regs t 9 = some b) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (scaleAfter ops t a b s) := by
  let sum := ops.add a b
  let mean := ops.div sum (ops.literal 128 1)
  let shifted := ops.add mean (ops.literal 1 100000)
  let s1 := setReg s t 4 sum 34
  let s2 := setReg s1 t 10 mean 35
  let s3 := setReg s2 t 11 shifted 36
  let s4 := setReg s3 t 12 (ops.rsqrt shifted) 37
  have e1 := execute_pure_of ops (layout p) (geometry p) t 4 34 (.bin .add (.reg 4) (.reg 9)) s sum
    (by simp [evalExpr, ha, hb, applyBinary, sum]) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have h1 : s1.regs t 4 = some sum := by simp [s1, setReg, advance]
  have e2 := execute_pure_of ops (layout p) (geometry p) t 10 35 (.bin .div (.reg 4) (.lit 128 1)) s1 mean
    (by simp [evalExpr, h1, applyBinary, mean]) (by simp [s1, setReg, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have h2 : s2.regs t 10 = some mean := by simp [s2, setReg, advance]
  have e3 := execute_pure_of ops (layout p) (geometry p) t 11 36 (.bin .add (.reg 10) (.lit 1 100000)) s2 shifted
    (by simp [evalExpr, h2, applyBinary, shifted]) (by simp [s2, setReg, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have h3 : s3.regs t 11 = some shifted := by simp [s3, setReg, advance]
  have e4 := execute_pure_of ops (layout p) (geometry p) t 12 37 (.un .rsqrt (.reg 11)) s3 (ops.rsqrt shifted)
    (by simp [evalExpr, h3, applyUnary]) (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  rewrite [scalar_step p neox ops t 33 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 34 _ _ s1 s2 (by cases neox <;> decide) (by simp [s1, setReg, advance]) e2]
  rewrite [scalar_step p neox ops t 35 _ _ s2 s3 (by cases neox <;> decide) (by simp [s2, setReg, advance]) e3]
  rewrite [scalar_step p neox ops t 36 _ _ s3 s4 (by cases neox <;> decide) (by simp [s3, setReg, advance]) e4]
  rfl

theorem scale_pc (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (scaleAfter ops t a b s).pc t = 37 := by simp [scaleAfter, setReg, advance]

theorem scale_value (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (scaleAfter ops t a b s).regs t 12 = some (normalScale ops (ops.add a b)) := by
  simp [scaleAfter, setReg, advance, normalScale]

theorem scale_acc (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (scaleAfter ops t a b s).regs t 4 = some (ops.add a b) := by simp [scaleAfter, setReg, advance]

theorem scale_input_reg (ops : Ops α) (t r : Nat) (a b : α) (s : State α) (hr : r < 4) :
    (scaleAfter ops t a b s).regs t r = s.regs t r := by
  have h4 : r ≠ 4 := by omega
  have h10 : r ≠ 10 := by omega
  have h11 : r ≠ 11 := by omega
  have h12 : r ≠ 12 := by omega
  simp [scaleAfter, setReg, advance, h4, h10, h11, h12]

theorem scale_preserves (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (scaleAfter ops t a b s).memory = s.memory ∧ (scaleAfter ops t a b s).trace = s.trace ∧
    (scaleAfter ops t a b s).epochs = s.epochs ∧ (scaleAfter ops t a b s).indices = s.indices := ⟨rfl, rfl, rfl, rfl⟩

theorem scale_other (ops : Ops α) (t u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (scaleAfter ops t a b s).pc u = s.pc u ∧ (scaleAfter ops t a b s).regs u = s.regs u := by
  constructor
  · simp [scaleAfter, setReg, advance, hu]
  · funext r; simp [scaleAfter, setReg, advance, hu]

#print axioms scale_eq
#print axioms scale_pc
#print axioms scale_value
#print axioms scale_acc
#print axioms scale_input_reg
#print axioms scale_preserves
#print axioms scale_other
end LarkNativeQKNormRope
