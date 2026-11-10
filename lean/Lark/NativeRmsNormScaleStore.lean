import Lark.NativeRmsNormMixedStage

/-! Actual source PC 53 through the thread-zero scale store and PC 55 barrier.
No full scale-phase or output completion theorem is asserted in this module.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scaleSlot (row : Nat) : Location := ⟨.shared, row, 1, 0⟩
def scaleFrom (ops : Ops α) (acc : α) : α :=
  ops.rsqrt (ops.add (ops.div acc (ops.literal 16384 1)) (ops.literal 1 100000))
def scaleExpr : Expr :=
  .un .rsqrt (.bin .add (.bin .div (.reg 0) (.lit 16384 1)) (.lit 1 100000))

def scaleWritten (t row : Nat) (value : α) (s : State α) : State α :=
  advance { record s t (scaleSlot row) true with
    memory := fun l => if l = scaleSlot row then some value else s.memory l } t 55

def scaleAfter (ops : Ops α) (t row tid : Nat) (acc : α) (s : State α) : State α :=
  if tid = 0 then scaleWritten t row (scaleFrom ops acc) (advance s t 54) else advance s t 55

theorem scale_branch_code : program[53]? = some (.scalar (.branch (.eq (.ivar 1) (.const 0)) 55)) := by decide
theorem scale_store_code : program[54]? = some (.scalar (.store .shared 1 (.const 0) scaleExpr)) := by decide

theorem eval_scale (p : Shape) (ops : Ops α) (t : Nat) (acc : α) (s : State α)
    (ha : s.regs t 0 = some acc) :
    evalExpr ops (layout p) (geometry p) t scaleExpr s = some (scaleFrom ops acc, s) := by
  simp [scaleExpr, scaleFrom, evalExpr, applyBinary, applyUnary, ha]

theorem scale_store_eq (p : Shape) (ops : Ops α) (t row : Nat) (acc : α) (s : State α)
    (hr : t / 1024 = row) (ha : s.regs t 0 = some acc) (hp : s.pc t = 54) :
    execute ops (layout p) (geometry p) t (.store .shared 1 (.const 0) scaleExpr) s =
      some (scaleWritten t row (scaleFrom ops acc) s) := by
  have hx : evalIndex (geometry p) t s (.const 0) = some 0 := rfl
  have hl : location (layout p) (geometry p) t .shared 1 0 true = some (scaleSlot row) := by
    simp [location, layout, geometry, scaleSlot, hr]
  simp only [execute, hx, bind, pure, Option.bind, hl, eval_scale p ops t acc s ha, hp]
  rfl

theorem scale_lane (p : Shape) (ops : Ops α) (t row tid extra : Nat) (acc : α) (s : State α)
    (hr : t / 1024 = row) (hi : s.indices t 1 = some (tid : Int))
    (ha : s.regs t 0 = some acc) (hp : s.pc t = 53) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s =
      some (scaleAfter ops t row tid acc s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some (decide (tid = 0)) := by
    simp [evalPredicate, evalIndex, hi, int32] <;> omega
  by_cases ht : tid = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some true := by simpa [ht] using heq
    let s1 := advance s t 54
    have h1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 55) s = some s1 := by
      simp only [execute, hg, hp, bind, pure, Option.bind]
      rfl
    have h2 := scale_store_eq p ops t row acc s1 hr ha (by simp [s1, advance])
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, scale_branch_code]) (by simpa only [hp] using scale_branch_code) h1]
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, s1, advance, scale_store_code])
      (by simpa only [s1, advance, ↓reduceIte] using scale_store_code) h2]
    have hcut : LarkCollective.parked program (scaleWritten t row (scaleFrom ops acc) s1) t = some .block := by
      unfold LarkCollective.parked
      simp only [scaleWritten, advance, ↓reduceIte]
      rewrite [second_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [scaleAfter, ht, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some false := by simpa [ht] using heq
    have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 55) s = some (advance s t 55) := by
      simp only [execute, hg, bind, pure, Option.bind]
      rfl
    rewrite [scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, scale_branch_code]) (by simpa only [hp] using scale_branch_code) he]
    have hcut : LarkCollective.parked program (advance s t 55) t = some .block := by
      unfold LarkCollective.parked
      simp only [advance, ↓reduceIte]
      rewrite [second_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [scaleAfter, ht, ↓reduceIte]

theorem scale_fields (ops : Ops α) (t row tid : Nat) (acc : α) (s : State α) :
    (scaleAfter ops t row tid acc s).pc t = 55 ∧
    (scaleAfter ops t row tid acc s).indices = s.indices ∧
    (scaleAfter ops t row tid acc s).regs = s.regs ∧
    (scaleAfter ops t row tid acc s).epochs = s.epochs := by
  unfold scaleAfter
  split <;> simp [scaleWritten, advance, record]

theorem scale_other (ops : Ops α) (t u row tid : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (scaleAfter ops t row tid acc s).pc u = s.pc u := by
  unfold scaleAfter
  split <;> simp [scaleWritten, advance, record, hu]

theorem scale_value (ops : Ops α) (t row : Nat) (acc : α) (s : State α) :
    (scaleAfter ops t row 0 acc s).memory (scaleSlot row) = some (scaleFrom ops acc) := by
  simp [scaleAfter, scaleWritten, advance, record]

theorem scale_memory_other (ops : Ops α) (t row tid : Nat) (acc : α) (s : State α)
    (l : Location) (hl : l ≠ scaleSlot row) : (scaleAfter ops t row tid acc s).memory l = s.memory l := by
  unfold scaleAfter
  split <;> simp [scaleWritten, advance, record, hl]

theorem scale_good (p : Shape) (ops : Ops α) (t row tid : Nat) (acc : α) (s : State α)
    (hr : t / 1024 = row) (ht : tid = t % 1024) (he : (s.epochs t).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (scaleAfter ops t row tid acc s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  by_cases hz : tid = 0
  · intro access ha
    simp only [scaleAfter, hz, ↓reduceIte, scaleWritten, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply LarkReductionFootprint.Good.scaleStore
      · rfl
      · exact hr.symm
      · rfl
      · rfl
      · change t % 1024 = 0
        omega
      · exact he
      · rfl
    · exact good access ha
  · simpa only [scaleAfter, hz, ↓reduceIte, advance] using good

#print axioms eval_scale
#print axioms scale_store_eq
#print axioms scale_lane
#print axioms scale_good
end LarkNativeRmsNorm
