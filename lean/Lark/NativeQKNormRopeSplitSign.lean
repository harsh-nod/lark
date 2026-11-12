import Lark.NativeQKNormRopeSplitExchange

/-! The actual lane<16 branch and source unary-negation lowering. The four
lower-half partners use literal-zero subtraction, with no algebraic assumptions. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setReg execute_pure_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitSignedPartner (ops : Ops α) (t : Nat) (value : α) : α :=
  if t % 32 < 16 then ops.sub (ops.literal 0 1) value else value

def splitNegateAt (ops : Ops α) (t e : Nat) (value : α) (s : State α) : State α :=
  setReg s t (25 + e) (ops.sub (ops.literal 0 1) value) (66 + e)

theorem split_negate_at_eq (p : Shape) (ops : Ops α) (t e extra : Nat) (value : α)
    (s : State α) (he : e < 4) (hp : s.pc t = 65 + e) (hv : s.regs t (25 + e) = some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (splitNegateAt ops t e value s) := by
  have code : (program true)[65 + e]? = some (.scalar (.assign (25 + e) (.bin .sub (.lit 0 1) (.reg (25 + e))))) := by
    have table : ∀ k : Fin 4, (program true)[65 + k.val]? =
        some (.scalar (.assign (25 + k.val) (.bin .sub (.lit 0 1) (.reg (25 + k.val))))) := by decide
    exact table ⟨e, he⟩
  have ex := execute_pure_of ops (layout p) (geometry p) t (25 + e) (66 + e)
    (.bin .sub (.lit 0 1) (.reg (25 + e))) s (ops.sub (ops.literal 0 1) value)
    (by simp [evalExpr, applyBinary, hv]) (by omega)
  exact scalar_step p true ops t (65 + e) extra _ s _ code hp ex

def splitNegated (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α) : State α :=
  splitNegateAt ops t 3 (values 3) (splitNegateAt ops t 2 (values 2)
    (splitNegateAt ops t 1 (values 1) (splitNegateAt ops t 0 (values 0) s)))

theorem split_negated_eq (p : Shape) (ops : Ops α) (t extra : Nat) (values : Nat → α)
    (s : State α) (hp : s.pc t = 65) (hv : ∀ e, e < 4 → s.regs t (25 + e) = some (values e)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (splitNegated ops t values s) := by
  let s1 := splitNegateAt ops t 0 (values 0) s
  let s2 := splitNegateAt ops t 1 (values 1) s1
  let s3 := splitNegateAt ops t 2 (values 2) s2
  rw [split_negate_at_eq p ops t 0 (extra + 3) (values 0) s (by decide) hp (hv 0 (by decide))]
  rw [split_negate_at_eq p ops t 1 (extra + 2) (values 1) s1 (by decide)
    (by simp [s1, splitNegateAt, setReg, advance])
    (by simpa [s1, splitNegateAt, setReg, advance] using hv 1 (by decide))]
  rw [split_negate_at_eq p ops t 2 (extra + 1) (values 2) s2 (by decide)
    (by simp [s2, splitNegateAt, setReg, advance])
    (by simpa [s2, s1, splitNegateAt, setReg, advance] using hv 2 (by decide))]
  rw [split_negate_at_eq p ops t 3 extra (values 3) s3 (by decide)
    (by simp [s3, splitNegateAt, setReg, advance])
    (by simpa [s3, s2, s1, splitNegateAt, setReg, advance] using hv 3 (by decide))]
  rfl

def splitSignSteps (t : Nat) : Nat := if t % 32 < 16 then 5 else 1
def splitSignStart (t : Nat) : Nat := if t % 32 < 16 then 65 else 69

def splitSigned (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α) : State α :=
  if t % 32 < 16 then splitNegated ops t values (advance s t 65) else advance s t 69

theorem split_sign_branch_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t = 64) (hi : s.indices t 3 = some ((t % 32 : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (advance s t (splitSignStart t)) := by
  have ex : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 3) (.const 16)) 69) s =
      some (advance s t (splitSignStart t)) := by
    by_cases lower : t % 32 < 16
    · have pred := predicate_lt_of (geometry p) t s (.ivar 3) (.const 16) ((t % 32 : Nat) : Int) 16 hi rfl (by omega)
      simp [execute, pred, hp, splitSignStart, lower]
    · have pred := predicate_nlt_of (geometry p) t s (.ivar 3) (.const 16) ((t % 32 : Nat) : Int) 16 hi rfl (by omega)
      simp [execute, pred, splitSignStart, lower]
  exact scalar_step p true ops t 64 extra _ s _ (by decide) hp ex

theorem split_signed_eq (p : Shape) (ops : Ops α) (t extra : Nat) (values : Nat → α)
    (s : State α) (hp : s.pc t = 64) (hi : s.indices t 3 = some ((t % 32 : Nat) : Int))
    (hv : ∀ e, e < 4 → s.regs t (25 + e) = some (values e)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + splitSignSteps t) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (splitSigned ops t values s) := by
  by_cases lower : t % 32 < 16
  · simp only [splitSignSteps, lower, if_true]
    rw [split_sign_branch_eq p ops t (extra + 4) s hp hi]
    simp only [splitSignStart, lower, if_true]
    rw [split_negated_eq p ops t extra values (advance s t 65) (by simp [advance]) hv]
    simp only [splitSigned, lower, if_true]
  · simp only [splitSignSteps, lower, if_false]
    rw [split_sign_branch_eq p ops t extra s hp hi]
    simp only [splitSignStart, splitSigned, lower, if_false]

theorem split_signed_pc (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α) :
    (splitSigned ops t values s).pc t = 69 := by
  unfold splitSigned
  split <;> simp [splitNegated, splitNegateAt, setReg, advance]

theorem split_signed_value (ops : Ops α) (t e : Nat) (values : Nat → α)
    (s : State α) (he : e < 4) (hv : ∀ e, e < 4 → s.regs t (25 + e) = some (values e)) :
    (splitSigned ops t values s).regs t (25 + e) = some (splitSignedPartner ops t (values e)) := by
  by_cases lower : t % 32 < 16
  · have choices : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;>
      simp [splitSigned, splitSignedPartner, lower, splitNegated, splitNegateAt, setReg, advance]
  · simpa only [splitSigned, splitSignedPartner, lower, if_false, advance] using hv e he

theorem split_signed_low (ops : Ops α) (t r : Nat) (values : Nat → α)
    (s : State α) (hr : r < 25) : (splitSigned ops t values s).regs t r = s.regs t r := by
  have h25 : r ≠ 25 := by omega
  have h26 : r ≠ 26 := by omega
  have h27 : r ≠ 27 := by omega
  have h28 : r ≠ 28 := by omega
  unfold splitSigned
  split <;> simp [splitNegated, splitNegateAt, setReg, advance, h25, h26, h27, h28]

theorem split_signed_preserves (ops : Ops α) (t : Nat) (values : Nat → α) (s : State α) :
    (splitSigned ops t values s).memory = s.memory ∧
    (splitSigned ops t values s).indices = s.indices ∧
    (splitSigned ops t values s).epochs = s.epochs ∧
    (splitSigned ops t values s).trace = s.trace := by
  unfold splitSigned
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem split_signed_other (ops : Ops α) (t u : Nat) (values : Nat → α)
    (s : State α) (hu : u ≠ t) :
    (splitSigned ops t values s).pc u = s.pc u ∧ (splitSigned ops t values s).regs u = s.regs u := by
  unfold splitSigned
  split <;> simp [splitNegated, splitNegateAt, setReg, advance, hu]

#print axioms split_negate_at_eq
#print axioms split_negated_eq
#print axioms split_sign_branch_eq
#print axioms split_signed_eq
#print axioms split_signed_pc
#print axioms split_signed_value
#print axioms split_signed_low
#print axioms split_signed_preserves
#print axioms split_signed_other
end LarkNativeQKNormRope
