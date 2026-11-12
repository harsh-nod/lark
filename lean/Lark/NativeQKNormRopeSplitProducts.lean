import Lark.NativeQKNormRopeSplitCache

/-! The three source-ordered multiply/multiply/add instructions for a
split-half output component. The partner has already passed the sign branch. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitComponent (ops : Ops α) (x partner cosine sine : α) : α :=
  ops.add (ops.mul x cosine) (ops.mul partner sine)

def splitProductsAfter (ops : Ops α) (t e : Nat) (x partner cosine sine : α) (s : State α) : State α :=
  let s := setReg s t (31 + 5 * e) (ops.mul x cosine) (74 + 7 * e)
  let s := setReg s t (32 + 5 * e) (ops.mul partner sine) (75 + 7 * e)
  setReg s t (33 + 5 * e) (splitComponent ops x partner cosine sine) (76 + 7 * e)

theorem split_products_eq (p : Shape) (ops : Ops α) (t e extra : Nat) (x partner cosine sine : α)
    (s : State α) (he : e < 4) (hp : s.pc t = 73 + 7 * e)
    (hx : s.regs t (18 + 2 * e) = some x) (hy : s.regs t (25 + e) = some partner)
    (hc : s.regs t (29 + 5 * e) = some cosine) (hs : s.regs t (30 + 5 * e) = some sine) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
        (splitProductsAfter ops t e x partner cosine sine s) := by
  let s1 := setReg s t (31 + 5 * e) (ops.mul x cosine) (74 + 7 * e)
  let s2 := setReg s1 t (32 + 5 * e) (ops.mul partner sine) (75 + 7 * e)
  let s3 := setReg s2 t (33 + 5 * e) (splitComponent ops x partner cosine sine) (76 + 7 * e)
  have e1 := execute_pure_of ops (layout p) (geometry p) t (31 + 5 * e) (74 + 7 * e)
    (.bin .mul (.reg (18 + 2 * e)) (.reg (29 + 5 * e))) s (ops.mul x cosine)
    (by simp [evalExpr, applyBinary, hx, hc]) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have hpy : s1.regs t (25 + e) = some partner := by
    have ne : 25 + e ≠ 31 + 5 * e := by omega
    simpa [s1, setReg, advance, ne] using hy
  have hps : s1.regs t (30 + 5 * e) = some sine := by
    have ne : 30 + 5 * e ≠ 31 + 5 * e := by omega
    simpa [s1, setReg, advance, ne] using hs
  have e2 := execute_pure_of ops (layout p) (geometry p) t (32 + 5 * e) (75 + 7 * e)
    (.bin .mul (.reg (25 + e)) (.reg (30 + 5 * e))) s1 (ops.mul partner sine)
    (by simp [evalExpr, applyBinary, hpy, hps]) (by simp [s1, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 := execute_pure_of ops (layout p) (geometry p) t (33 + 5 * e) (76 + 7 * e)
    (.bin .add (.reg (31 + 5 * e)) (.reg (32 + 5 * e))) s2 (splitComponent ops x partner cosine sine)
    (by
      have ne : 31 + 5 * e ≠ 32 + 5 * e := by omega
      simp [evalExpr, applyBinary, s2, s1, setReg, advance, ne, splitComponent])
    (by simp [s2, setReg, advance] <;> omega)
  change execute _ _ _ _ _ s2 = some s3 at e3
  have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  have code1 : (program true)[73 + 7 * e]? =
      some (.scalar (.assign (31 + 5 * e) (.bin .mul (.reg (18 + 2 * e)) (.reg (29 + 5 * e))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  have code2 : (program true)[74 + 7 * e]? =
      some (.scalar (.assign (32 + 5 * e) (.bin .mul (.reg (25 + e)) (.reg (30 + 5 * e))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  have code3 : (program true)[75 + 7 * e]? =
      some (.scalar (.assign (33 + 5 * e) (.bin .add (.reg (31 + 5 * e)) (.reg (32 + 5 * e))))) := by
    rcases choices with rfl | rfl | rfl | rfl <;> decide
  rw [scalar_step p true ops t (73 + 7 * e) (extra + 2) _ s s1 code1 hp e1]
  rw [scalar_step p true ops t (74 + 7 * e) (extra + 1) _ s1 s2 code2
    (by simp [s1, setReg, advance]) e2]
  rw [scalar_step p true ops t (75 + 7 * e) extra _ s2 s3 code3
    (by simp [s2, setReg, advance]) e3]
  rfl

theorem split_products_pc (ops : Ops α) (t e : Nat) (x partner cosine sine : α) (s : State α) :
    (splitProductsAfter ops t e x partner cosine sine s).pc t = 76 + 7 * e := by
  simp [splitProductsAfter, setReg, advance]

theorem split_products_value (ops : Ops α) (t e : Nat) (x partner cosine sine : α) (s : State α) :
    (splitProductsAfter ops t e x partner cosine sine s).regs t (33 + 5 * e) =
      some (splitComponent ops x partner cosine sine) := by
  simp [splitProductsAfter, setReg, advance]

theorem split_products_low (ops : Ops α) (t e r : Nat) (x partner cosine sine : α)
    (s : State α) (hr : r < 31 + 5 * e) :
    (splitProductsAfter ops t e x partner cosine sine s).regs t r = s.regs t r := by
  have n1 : r ≠ 31 + 5 * e := by omega
  have n2 : r ≠ 32 + 5 * e := by omega
  have n3 : r ≠ 33 + 5 * e := by omega
  simp [splitProductsAfter, setReg, advance, n1, n2, n3]

theorem split_products_preserves (ops : Ops α) (t e : Nat) (x partner cosine sine : α) (s : State α) :
    (splitProductsAfter ops t e x partner cosine sine s).memory = s.memory ∧
    (splitProductsAfter ops t e x partner cosine sine s).indices = s.indices ∧
    (splitProductsAfter ops t e x partner cosine sine s).epochs = s.epochs ∧
    (splitProductsAfter ops t e x partner cosine sine s).trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

theorem split_products_other (ops : Ops α) (t e u : Nat) (x partner cosine sine : α)
    (s : State α) (hu : u ≠ t) :
    (splitProductsAfter ops t e x partner cosine sine s).pc u = s.pc u ∧
    (splitProductsAfter ops t e x partner cosine sine s).regs u = s.regs u := by
  simp [splitProductsAfter, setReg, advance, hu]

#print axioms split_products_eq
#print axioms split_products_pc
#print axioms split_products_value
#print axioms split_products_low
#print axioms split_products_preserves
#print axioms split_products_other
end LarkNativeQKNormRope
