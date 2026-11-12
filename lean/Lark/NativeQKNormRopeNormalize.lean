import Lark.NativeQKNormRopeWeightLoad

/-! Eight actual products at PCs51..58. The source computes x*(scale*weight)
and keeps FP32 registers until the later rotary output conversion. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normalizedValue (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α) (e : Nat) : α :=
  ops.mul (inputValue ops input t e) (ops.mul scale (weightValue ops input t buffer e))

structure NormalizeReady (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (s : State α) : Prop where
  values : InputValues ops input t s
  weights : ∀ e, e < 4 → s.regs t (13 + e) = some (weightValue ops input t buffer e)
  scaleReg : s.regs t 12 = some scale

def normalizeAt (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α) (e : Nat)
    (s : State α) : State α :=
  let s := setReg s t (17 + 2 * e) (ops.mul scale (weightValue ops input t buffer e)) (52 + 2 * e)
  setReg s t (18 + 2 * e) (normalizedValue ops input t buffer scale e) (53 + 2 * e)

theorem normalize_at_pc (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (e : Nat) (s : State α) : (normalizeAt ops input t buffer scale e s).pc t = 53 + 2 * e := by
  simp [normalizeAt, setReg, advance]

theorem normalize_at_low (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (e r : Nat) (s : State α) (hr : r < 17) :
    (normalizeAt ops input t buffer scale e s).regs t r = s.regs t r := by
  have ht : r ≠ 17 + 2 * e := by omega
  have ho : r ≠ 18 + 2 * e := by omega
  simp [normalizeAt, setReg, advance, ht, ho]

theorem normalize_at_ready (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (e : Nat) (s : State α) (ready : NormalizeReady ops input t buffer scale s) :
    NormalizeReady ops input t buffer scale (normalizeAt ops input t buffer scale e s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (normalize_at_low ops input t buffer scale e r s (by omega)).trans (ready.values r hr)
  · intro r hr
    exact (normalize_at_low ops input t buffer scale e (13 + r) s (by omega)).trans (ready.weights r hr)
  · exact (normalize_at_low ops input t buffer scale e 12 s (by decide)).trans ready.scaleReg

theorem normalize_at_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t buffer : Nat) (scale : α) (e extra : Nat) (s : State α) (he : e < 4)
    (hp : s.pc t = 51 + 2 * e) (ready : NormalizeReady ops input t buffer scale s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra
        (normalizeAt ops input t buffer scale e s) := by
  let product := ops.mul scale (weightValue ops input t buffer e)
  let s1 := setReg s t (17 + 2 * e) product (52 + 2 * e)
  have e1 := execute_pure_of ops (layout p) (geometry p) t (17 + 2 * e) (52 + 2 * e)
    (.bin .mul (.reg 12) (.reg (13 + e))) s product
    (by simp [evalExpr, ready.scaleReg, ready.weights e he, applyBinary, product]) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have hne : e ≠ 17 + 2 * e := by omega
  have hx : s1.regs t e = some (inputValue ops input t e) := by
    simpa [s1, setReg, advance, hne] using ready.values e he
  have hm : s1.regs t (17 + 2 * e) = some product := by simp [s1, setReg, advance]
  have e2 := execute_pure_of ops (layout p) (geometry p) t (18 + 2 * e) (53 + 2 * e)
    (.bin .mul (.reg e) (.reg (17 + 2 * e))) s1 (normalizedValue ops input t buffer scale e)
    (by simp [evalExpr, hx, hm, applyBinary, normalizedValue, product])
    (by simp [s1, setReg, advance] <;> omega)
  have code1 : (program neox)[51 + 2 * e]? =
      some (.scalar (.assign (17 + 2 * e) (.bin .mul (.reg 12) (.reg (13 + e))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  have code2 : (program neox)[52 + 2 * e]? =
      some (.scalar (.assign (18 + 2 * e) (.bin .mul (.reg e) (.reg (17 + 2 * e))))) := by
    have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> cases neox <;> decide
  rewrite [scalar_step p neox ops t (51 + 2 * e) (extra + 1) _ s s1 code1 hp e1]
  rewrite [scalar_step p neox ops t (52 + 2 * e) extra _ s1 _ code2
    (by simp [s1, setReg, advance]) e2]
  rfl

def normalizedFour (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (s : State α) : State α :=
  normalizeAt ops input t buffer scale 3 (normalizeAt ops input t buffer scale 2
    (normalizeAt ops input t buffer scale 1 (normalizeAt ops input t buffer scale 0 s)))

theorem normalized_four_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t buffer : Nat) (scale : α) (extra : Nat) (s : State α) (hp : s.pc t = 51)
    (ready : NormalizeReady ops input t buffer scale s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra
        (normalizedFour ops input t buffer scale s) := by
  let s1 := normalizeAt ops input t buffer scale 0 s
  let s2 := normalizeAt ops input t buffer scale 1 s1
  let s3 := normalizeAt ops input t buffer scale 2 s2
  have r1 := normalize_at_ready ops input t buffer scale 0 s ready
  have r2 := normalize_at_ready ops input t buffer scale 1 s1 r1
  have r3 := normalize_at_ready ops input t buffer scale 2 s2 r2
  rewrite [normalize_at_eq p neox ops input t buffer scale 0 (extra + 6) s (by decide) hp ready]
  rewrite [normalize_at_eq p neox ops input t buffer scale 1 (extra + 4) s1 (by decide)
    (normalize_at_pc ops input t buffer scale 0 s) r1]
  rewrite [normalize_at_eq p neox ops input t buffer scale 2 (extra + 2) s2 (by decide)
    (normalize_at_pc ops input t buffer scale 1 s1) r2]
  rewrite [normalize_at_eq p neox ops input t buffer scale 3 extra s3 (by decide)
    (normalize_at_pc ops input t buffer scale 2 s2) r3]
  rfl

theorem normalized_four_pc (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (s : State α) : (normalizedFour ops input t buffer scale s).pc t = 59 := by
  exact normalize_at_pc ops input t buffer scale 3 _

theorem normalized_four_value (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (e : Nat) (s : State α) (he : e < 4) :
    (normalizedFour ops input t buffer scale s).regs t (18 + 2 * e) =
      some (normalizedValue ops input t buffer scale e) := by
  have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> simp [normalizedFour, normalizeAt, setReg, advance]

theorem normalized_four_low (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (r : Nat) (s : State α) (hr : r < 17) :
    (normalizedFour ops input t buffer scale s).regs t r = s.regs t r := by
  simp only [normalizedFour, normalize_at_low ops input t buffer scale _ r _ hr]

theorem normalized_four_preserves (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (s : State α) :
    (normalizedFour ops input t buffer scale s).memory = s.memory ∧
    (normalizedFour ops input t buffer scale s).indices = s.indices ∧
    (normalizedFour ops input t buffer scale s).epochs = s.epochs ∧
    (normalizedFour ops input t buffer scale s).trace = s.trace := ⟨rfl, rfl, rfl, rfl⟩

theorem normalized_four_other (ops : Ops α) (input : Nat → Nat → α) (t buffer : Nat) (scale : α)
    (u : Nat) (s : State α) (hu : u ≠ t) :
    (normalizedFour ops input t buffer scale s).pc u = s.pc u ∧
    (normalizedFour ops input t buffer scale s).regs u = s.regs u := by
  constructor
  · simp [normalizedFour, normalizeAt, setReg, advance, hu]
  · funext r; simp [normalizedFour, normalizeAt, setReg, advance, hu]

#print axioms normalize_at_pc
#print axioms normalize_at_low
#print axioms normalize_at_ready
#print axioms normalize_at_eq
#print axioms normalized_four_eq
#print axioms normalized_four_pc
#print axioms normalized_four_value
#print axioms normalized_four_low
#print axioms normalized_four_preserves
#print axioms normalized_four_other
end LarkNativeQKNormRope
