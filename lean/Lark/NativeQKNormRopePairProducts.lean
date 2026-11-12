import Lark.NativeQKNormRopeCache

/-! Actual six-product/add/subtract rotary suffix for either interleaved pair.
The imaginary component retains source order: (x*sin) + (y*cos). -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedReal (ops : Ops α) (x y c sn : α) : α := ops.sub (ops.mul x c) (ops.mul y sn)
def interleavedImaginary (ops : Ops α) (x y c sn : α) : α := ops.add (ops.mul x sn) (ops.mul y c)

def pairProductsAfter (ops : Ops α) (t pair : Nat) (x y c sn : α) (s : State α) : State α :=
  let s := setReg s t (27 + 8 * pair) (ops.mul x c) (64 + 10 * pair)
  let s := setReg s t (28 + 8 * pair) (ops.mul y sn) (65 + 10 * pair)
  let s := setReg s t (29 + 8 * pair) (ops.mul x sn) (66 + 10 * pair)
  let s := setReg s t (30 + 8 * pair) (ops.mul y c) (67 + 10 * pair)
  let s := setReg s t (31 + 8 * pair) (interleavedReal ops x y c sn) (68 + 10 * pair)
  setReg s t (32 + 8 * pair) (interleavedImaginary ops x y c sn) (69 + 10 * pair)

theorem reg_before_set (s : State α) (t r dest pc : Nat) (value : α) (hr : r < dest) :
    (setReg s t dest value pc).regs t r = s.regs t r := by
  simp [setReg, advance, Nat.ne_of_lt hr]

theorem pair_products_eq (p : Shape) (ops : Ops α) (t pair extra : Nat) (x y c sn : α)
    (s : State α) (hj : pair < 2) (hp : s.pc t = 63 + 10 * pair)
    (hx : s.regs t (18 + 4 * pair) = some x) (hy : s.regs t (20 + 4 * pair) = some y)
    (hc : s.regs t (25 + 8 * pair) = some c) (hs : s.regs t (26 + 8 * pair) = some sn) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra + 6) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program false) t extra
        (pairProductsAfter ops t pair x y c sn s) := by
  let s1 := setReg s t (27 + 8 * pair) (ops.mul x c) (64 + 10 * pair)
  let s2 := setReg s1 t (28 + 8 * pair) (ops.mul y sn) (65 + 10 * pair)
  let s3 := setReg s2 t (29 + 8 * pair) (ops.mul x sn) (66 + 10 * pair)
  let s4 := setReg s3 t (30 + 8 * pair) (ops.mul y c) (67 + 10 * pair)
  let s5 := setReg s4 t (31 + 8 * pair) (interleavedReal ops x y c sn) (68 + 10 * pair)
  let s6 := setReg s5 t (32 + 8 * pair) (interleavedImaginary ops x y c sn) (69 + 10 * pair)
  have f1 : ∀ r, r < 27 + 8 * pair → s1.regs t r = s.regs t r := by
    intro r hr; exact reg_before_set s t r _ _ _ hr
  have f2 : ∀ r, r < 27 + 8 * pair → s2.regs t r = s.regs t r := by
    intro r hr; exact (reg_before_set s1 t r _ _ _ (by omega)).trans (f1 r hr)
  have f3 : ∀ r, r < 27 + 8 * pair → s3.regs t r = s.regs t r := by
    intro r hr; exact (reg_before_set s2 t r _ _ _ (by omega)).trans (f2 r hr)
  have e1 := execute_pure_of ops (layout p) (geometry p) t (27 + 8 * pair) (64 + 10 * pair)
    (.bin .mul (.reg (18 + 4 * pair)) (.reg (25 + 8 * pair))) s (ops.mul x c)
    (by simp [evalExpr, applyBinary, hx, hc]) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have e2 := execute_pure_of ops (layout p) (geometry p) t (28 + 8 * pair) (65 + 10 * pair)
    (.bin .mul (.reg (20 + 4 * pair)) (.reg (26 + 8 * pair))) s1 (ops.mul y sn)
    (by simp [evalExpr, applyBinary, f1 (20 + 4 * pair) (by omega), f1 (26 + 8 * pair) (by omega), hy, hs])
    (by simp [s1, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 := execute_pure_of ops (layout p) (geometry p) t (29 + 8 * pair) (66 + 10 * pair)
    (.bin .mul (.reg (18 + 4 * pair)) (.reg (26 + 8 * pair))) s2 (ops.mul x sn)
    (by simp [evalExpr, applyBinary, f2 (18 + 4 * pair) (by omega), f2 (26 + 8 * pair) (by omega), hx, hs])
    (by simp [s2, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_pure_of ops (layout p) (geometry p) t (30 + 8 * pair) (67 + 10 * pair)
    (.bin .mul (.reg (20 + 4 * pair)) (.reg (25 + 8 * pair))) s3 (ops.mul y c)
    (by simp [evalExpr, applyBinary, f3 (20 + 4 * pair) (by omega), f3 (25 + 8 * pair) (by omega), hy, hc])
    (by simp [s3, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 := execute_pure_of ops (layout p) (geometry p) t (31 + 8 * pair) (68 + 10 * pair)
    (.bin .sub (.reg (27 + 8 * pair)) (.reg (28 + 8 * pair))) s4 (interleavedReal ops x y c sn)
    (by simp [evalExpr, applyBinary, s4, s3, s2, s1, setReg, advance, interleavedReal])
    (by simp [s4, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s4 = some s5 at e5
  have e6 := execute_pure_of ops (layout p) (geometry p) t (32 + 8 * pair) (69 + 10 * pair)
    (.bin .add (.reg (29 + 8 * pair)) (.reg (30 + 8 * pair))) s5 (interleavedImaginary ops x y c sn)
    (by simp [evalExpr, applyBinary, s5, s4, s3, setReg, advance, interleavedImaginary])
    (by simp [s5, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s5 = some s6 at e6
  have choices : pair = 0 ∨ pair = 1 := by omega
  have code1 : (program false)[63 + 10 * pair]? = some (.scalar
      (.assign (27 + 8 * pair) (.bin .mul (.reg (18 + 4 * pair)) (.reg (25 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  have code2 : (program false)[64 + 10 * pair]? = some (.scalar
      (.assign (28 + 8 * pair) (.bin .mul (.reg (20 + 4 * pair)) (.reg (26 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  have code3 : (program false)[65 + 10 * pair]? = some (.scalar
      (.assign (29 + 8 * pair) (.bin .mul (.reg (18 + 4 * pair)) (.reg (26 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  have code4 : (program false)[66 + 10 * pair]? = some (.scalar
      (.assign (30 + 8 * pair) (.bin .mul (.reg (20 + 4 * pair)) (.reg (25 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  have code5 : (program false)[67 + 10 * pair]? = some (.scalar
      (.assign (31 + 8 * pair) (.bin .sub (.reg (27 + 8 * pair)) (.reg (28 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  have code6 : (program false)[68 + 10 * pair]? = some (.scalar
      (.assign (32 + 8 * pair) (.bin .add (.reg (29 + 8 * pair)) (.reg (30 + 8 * pair))))) := by
    rcases choices with rfl | rfl <;> decide
  rewrite [scalar_step p false ops t (63 + 10 * pair) (extra + 5) _ s s1 code1 hp e1]
  rewrite [scalar_step p false ops t (64 + 10 * pair) (extra + 4) _ s1 s2 code2 (by simp [s1, setReg, advance]) e2]
  rewrite [scalar_step p false ops t (65 + 10 * pair) (extra + 3) _ s2 s3 code3 (by simp [s2, setReg, advance]) e3]
  rewrite [scalar_step p false ops t (66 + 10 * pair) (extra + 2) _ s3 s4 code4 (by simp [s3, setReg, advance]) e4]
  rewrite [scalar_step p false ops t (67 + 10 * pair) (extra + 1) _ s4 s5 code5 (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p false ops t (68 + 10 * pair) extra _ s5 s6 code6 (by simp [s5, setReg, advance]) e6]
  rfl

theorem pair_products_pc (ops : Ops α) (t pair : Nat) (x y c sn : α) (s : State α) :
    (pairProductsAfter ops t pair x y c sn s).pc t = 69 + 10 * pair := by
  simp [pairProductsAfter, setReg, advance]

theorem pair_products_values (ops : Ops α) (t pair : Nat) (x y c sn : α) (s : State α) :
    (pairProductsAfter ops t pair x y c sn s).regs t (31 + 8 * pair) = some (interleavedReal ops x y c sn) ∧
    (pairProductsAfter ops t pair x y c sn s).regs t (32 + 8 * pair) = some (interleavedImaginary ops x y c sn) := by
  simp [pairProductsAfter, setReg, advance]

theorem pair_products_low_reg (ops : Ops α) (t pair r : Nat) (x y c sn : α)
    (s : State α) (hr : r < 27 + 8 * pair) :
    (pairProductsAfter ops t pair x y c sn s).regs t r = s.regs t r := by
  have h27 : r ≠ 27 + 8 * pair := by omega
  have h28 : r ≠ 28 + 8 * pair := by omega
  have h29 : r ≠ 29 + 8 * pair := by omega
  have h30 : r ≠ 30 + 8 * pair := by omega
  have h31 : r ≠ 31 + 8 * pair := by omega
  have h32 : r ≠ 32 + 8 * pair := by omega
  simp [pairProductsAfter, setReg, advance, h27, h28, h29, h30, h31, h32]

theorem pair_products_preserves (ops : Ops α) (t pair : Nat) (x y c sn : α) (s : State α) :
    (pairProductsAfter ops t pair x y c sn s).memory = s.memory ∧
    (pairProductsAfter ops t pair x y c sn s).indices = s.indices ∧
    (pairProductsAfter ops t pair x y c sn s).epochs = s.epochs ∧
    (pairProductsAfter ops t pair x y c sn s).trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

theorem pair_products_other (ops : Ops α) (t pair u : Nat) (x y c sn : α)
    (s : State α) (hu : u ≠ t) :
    (pairProductsAfter ops t pair x y c sn s).pc u = s.pc u ∧
    (pairProductsAfter ops t pair x y c sn s).regs u = s.regs u := by
  constructor
  · simp [pairProductsAfter, setReg, advance, hu]
  · funext r; simp [pairProductsAfter, setReg, advance, hu]

#print axioms reg_before_set
#print axioms pair_products_eq
#print axioms pair_products_pc
#print axioms pair_products_values
#print axioms pair_products_low_reg
#print axioms pair_products_preserves
#print axioms pair_products_other
end LarkNativeQKNormRope
