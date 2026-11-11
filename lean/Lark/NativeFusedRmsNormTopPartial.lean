import Lark.NativeFusedRmsNormLogicalStages

/-! Actual final block-reduction add and tid-zero store into shared partial0.
The result is the source-ordered value of logical lane zero, not a claimed
uniform value across lanes under arbitrary arithmetic operations.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def topCell (t : Nat) : Location := partialCell t 0
def topWritten (t : Nat) (value : α) (s : State α) : State α := written t 50 (topCell t) value s
def topAfter (t tid : Nat) (value : α) (s : State α) : State α :=
  if tid = 0 then topWritten t value (advance s t 49) else advance s t 50

theorem top_branch_code : program[48]? = some (.scalar (.branch (.eq (.ivar 1) (.const 0)) 50)) := by decide
theorem top_store_code : program[49]? = some (.scalar (.store .shared 0 (.const 0) (.reg 0))) := by decide

theorem top_location (p : Shape) (t : Nat) :
    location (layout p) (geometry p) t .shared 0 0 true = some (topCell t) :=
  partial_location p t 0 (by decide)

theorem top_store_eq (p : Shape) (ops : Ops α) (t : Nat) (value : α) (s : State α)
    (ha : s.regs t 0 = some value) (hp : s.pc t = 49) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.const 0) (.reg 0)) s =
      some (topWritten t value s) := by
  simp [execute, evalIndex, top_location p t, evalExpr, ha, hp, topWritten, written, record, int32]

theorem top_lane (p : Shape) (ops : Ops α) (t tid extra : Nat) (value : α) (s : State α)
    (hi : s.indices t 1 = some (tid : Int)) (ha : s.regs t 0 = some value) (hp : s.pc t = 48) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s = some (topAfter t tid value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some (decide (tid = 0)) := by
    simp [evalPredicate, evalIndex, hi, int32] <;> omega
  by_cases hz : tid = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some true := by simpa [hz] using heq
    let s1 := advance s t 49
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 50) s = some s1 := by
      simp [execute, hg, hp, s1]
    have e2 := top_store_eq p ops t value s1 ha (by simp [s1, advance])
    rewrite [scalar_step p ops t 48 _ _ s s1 top_branch_code hp e1,
      scalar_step p ops t 49 _ _ s1 _ top_store_code (by simp [s1, advance]) e2]
    have hcut : LarkCollective.parked program (topWritten t value s1) t = some .block := by
      simp only [LarkCollective.parked, topWritten, written, advance, ↓reduceIte, second_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [topAfter, hz, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 1) (.const 0)) = some false := by simpa [hz] using heq
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 1) (.const 0)) 50) s = some (advance s t 50) := by
      simp [execute, hg]
    rewrite [scalar_step p ops t 48 _ _ s _ top_branch_code hp e1]
    have hcut : LarkCollective.parked program (advance s t 50) t = some .block := by
      simp only [LarkCollective.parked, advance, ↓reduceIte, second_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [topAfter, hz, ↓reduceIte]

theorem top_fields (t tid : Nat) (value : α) (s : State α) :
    (topAfter t tid value s).pc t = 50 ∧ (topAfter t tid value s).indices = s.indices ∧
    (topAfter t tid value s).regs = s.regs ∧ (topAfter t tid value s).epochs = s.epochs := by
  unfold topAfter
  split <;> simp [topWritten, written, advance, record]

theorem top_other (t u tid : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (topAfter t tid value s).pc u = s.pc u := by
  unfold topAfter
  split <;> simp [topWritten, written, advance, record, hu]

theorem top_memory_other (t tid : Nat) (value : α) (s : State α) (l : Location) (hl : l ≠ topCell t) :
    (topAfter t tid value s).memory l = s.memory l := by
  unfold topAfter
  split <;> simp [topWritten, written_memory, advance, hl]

theorem top_value (t : Nat) (value : α) (s : State α) :
    (topAfter t 0 value s).memory (topCell t) = some value := by
  simp [topAfter, topWritten, written_memory, advance]

theorem top_good (t tid : Nat) (value : α) (s : State α)
    (hi : t % 1024 = tid) (he : (s.epochs t).block = 1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (topAfter t tid value s).trace, Good a := by
  by_cases hz : tid = 0
  · intro a ha
    simp only [topAfter, hz, ↓reduceIte, topWritten, written, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Good.blockStore rfl rfl rfl rfl (hi.trans hz) he rfl
    · exact good a ha
  · simpa only [topAfter, hz, ↓reduceIte, advance] using good

def secondLastAfter (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  topAfter t (t % 1024) (ops.add a b) (addAfter ops t 47 a b s)

theorem second_last_lane (p : Shape) (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (hi : NativeIndices t s) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = 47) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some (secondLastAfter ops t a b s) := by
  rewrite [show fuel.lane = 511 + 1 by decide, add_eq p ops t 47 511 a b s hp ha hb (by decide)]
  apply top_lane p ops t (t % 1024) 508 (ops.add a b) (addAfter ops t 47 a b s) hi.2.1
  · simp [addAfter, LarkReduction.setReg, advance]
  · simp [addAfter, LarkReduction.setReg, advance]

theorem second_last_fields (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (secondLastAfter ops t a b s).pc t = 50 ∧
    (secondLastAfter ops t a b s).regs t 0 = some (ops.add a b) ∧
    (secondLastAfter ops t a b s).indices = s.indices ∧ (secondLastAfter ops t a b s).epochs = s.epochs := by
  have h := top_fields t (t % 1024) (ops.add a b) (addAfter ops t 47 a b s)
  refine ⟨h.1, ?_, h.2.1, h.2.2.2⟩
  rewrite [show (secondLastAfter ops t a b s).regs = (addAfter ops t 47 a b s).regs from h.2.2.1]
  simp [addAfter, LarkReduction.setReg, advance]

theorem second_last_other (ops : Ops α) (t u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (secondLastAfter ops t a b s).pc u = s.pc u ∧ (secondLastAfter ops t a b s).regs u = s.regs u := by
  have h := top_fields t (t % 1024) (ops.add a b) (addAfter ops t 47 a b s)
  have other := add_other ops t 47 u a b s hu
  exact ⟨(top_other t u _ _ _ hu).trans other.1, (congrFun h.2.2.1 u).trans other.2⟩

theorem second_last_good (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (he : (s.epochs t).block = 1) (good : ∀ a ∈ s.trace, Good a) :
    ∀ access ∈ (secondLastAfter ops t a b s).trace, Good access := top_good t _ _ _ rfl he good

#print axioms top_lane
#print axioms top_fields
#print axioms top_value
#print axioms top_good
#print axioms second_last_lane
#print axioms second_last_fields
#print axioms second_last_other
#print axioms second_last_good
end LarkNativeFusedRmsNorm
