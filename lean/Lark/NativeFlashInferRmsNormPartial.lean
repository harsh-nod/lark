import Lark.NativeFlashInferRmsNormFirstStages

/-! Actual final XOR add, logical-lane-zero partial store and first barrier.
Each native wave has two distinct partial writers, one per logical32 group.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def partialCell (t warp : Nat) : Location := ⟨.shared, t / 1024, 0, warp⟩
def partialWritten (t warp : Nat) (value : α) (s : State α) : State α :=
  written t 31 (partialCell t warp) value s
def partialAfter (t lane warp : Nat) (value : α) (s : State α) : State α :=
  if lane = 0 then partialWritten t warp value (advance s t 30) else advance s t 31

theorem partial_branch_code :
    program[29]? = some (.scalar (.branch (.eq (.ivar 2) (.const 0)) 31)) := by decide
theorem partial_store_code :
    program[30]? = some (.scalar (.store .shared 0 (.ivar 3) (.reg 0))) := by decide

theorem partial_location (p : Shape) (t warp : Nat) (hw : warp < 32) :
    location (layout p) (geometry p) t .shared 0 (warp : Int) true = some (partialCell t warp) := by
  simp [location, layout, geometry, partialCell, show ¬ (warp : Int) < 0 by omega, hw]

theorem partial_store_eq (p : Shape) (ops : Ops α) (t warp : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi : s.indices t 3 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t = 30) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.ivar 3) (.reg 0)) s =
      some (partialWritten t warp value s) := by
  simp [execute, evalIndex, hi, partial_location p t warp hw, evalExpr, ha, hp, partialWritten, written, record]

theorem partial_lane (p : Shape) (ops : Ops α) (t lane warp extra : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi2 : s.indices t 2 = some (lane : Int))
    (hi3 : s.indices t 3 = some (warp : Int)) (ha : s.regs t 0 = some value) (hp : s.pc t = 29) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 3) s =
      some (partialAfter t lane warp value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some (decide (lane = 0)) := by
    simp [evalPredicate, evalIndex, hi2, int32] <;> omega
  by_cases hl : lane = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some true := by simpa [hl] using heq
    let s1 := advance s t 30
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 31) s = some s1 := by
      simp [execute, hg, hp, s1]
    have e2 := partial_store_eq p ops t warp value s1 hw hi3 ha (by simp [s1, advance])
    rewrite [scalar_step p ops t 29 _ _ s s1 partial_branch_code hp e1]
    rewrite [scalar_step p ops t 30 _ _ s1 _ partial_store_code (by simp [s1, advance]) e2]
    have hcut : LarkCollective.parked program (partialWritten t warp value s1) t = some .block := by
      simp only [LarkCollective.parked, partialWritten, written, advance, ↓reduceIte]
      rewrite [first_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some false := by simpa [hl] using heq
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 31) s =
        some (advance s t 31) := by simp [execute, hg]
    rewrite [scalar_step p ops t 29 _ _ s _ partial_branch_code hp e1]
    have hcut : LarkCollective.parked program (advance s t 31) t = some .block := by
      simp only [LarkCollective.parked, advance, ↓reduceIte]
      rewrite [first_barrier]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]

theorem partial_fields (t lane warp : Nat) (value : α) (s : State α) :
    (partialAfter t lane warp value s).pc t = 31 ∧
    (partialAfter t lane warp value s).indices = s.indices ∧
    (partialAfter t lane warp value s).regs = s.regs ∧
    (partialAfter t lane warp value s).epochs = s.epochs := by
  unfold partialAfter
  split <;> simp [partialWritten, written, advance, record]

theorem partial_other (t u lane warp : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (partialAfter t lane warp value s).pc u = s.pc u := by
  unfold partialAfter
  split <;> simp [partialWritten, written, advance, record, hu]

theorem partial_memory_other (t lane warp : Nat) (value : α) (s : State α) (l : Location)
    (hl : l ≠ partialCell t warp) : (partialAfter t lane warp value s).memory l = s.memory l := by
  unfold partialAfter
  split <;> simp [partialWritten, written_memory, advance, hl]

theorem partial_value (t warp : Nat) (value : α) (s : State α) :
    (partialAfter t 0 warp value s).memory (partialCell t warp) = some value := by
  simp [partialAfter, partialWritten, written_memory, advance]

theorem partial_good (t lane warp : Nat) (value : α) (s : State α)
    (hl : lane = (t % 1024) % 32) (hw : warp = (t % 1024) / 32) (he : (s.epochs t).block = 0)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (partialAfter t lane warp value s).trace, Good a := by
  by_cases hz : lane = 0
  · intro a ha
    simp only [partialAfter, hz, ↓reduceIte, partialWritten, written, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply Good.partialStore rfl rfl rfl
      · change t % 1024 = warp * 32
        omega
      · exact he
      · rfl
    · exact good a ha
  · simpa only [partialAfter, hz, ↓reduceIte, advance] using good

def firstLastAfter (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  partialAfter t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (addAfter ops t 28 a b s)

theorem first_last_lane (p : Shape) (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (hi : NativeIndices t s) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) (hp : s.pc t = 28) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (firstLastAfter ops t a b s) := by
  rewrite [show fuel.lane = 511 + 1 by decide,
    add_eq p ops t 28 511 a b s hp ha hb (by decide)]
  apply partial_lane p ops t ((t % 1024) % 32) ((t % 1024) / 32) 508 (ops.add a b) (addAfter ops t 28 a b s)
    (by omega) hi.2.2.1 hi.2.2.2
  · simp [addAfter, LarkReduction.setReg, advance]
  · simp [addAfter, LarkReduction.setReg, advance]

theorem first_last_fields (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (firstLastAfter ops t a b s).pc t = 31 ∧
    (firstLastAfter ops t a b s).regs t 0 = some (ops.add a b) ∧
    (firstLastAfter ops t a b s).indices = s.indices ∧
    (firstLastAfter ops t a b s).epochs = s.epochs := by
  have h := partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (addAfter ops t 28 a b s)
  refine ⟨h.1, ?_, h.2.1, h.2.2.2⟩
  rewrite [show (firstLastAfter ops t a b s).regs = (addAfter ops t 28 a b s).regs from h.2.2.1]
  simp [addAfter, LarkReduction.setReg, advance]

theorem first_last_other (ops : Ops α) (t u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (firstLastAfter ops t a b s).pc u = s.pc u ∧
    (firstLastAfter ops t a b s).regs u = s.regs u := by
  have h := partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.add a b) (addAfter ops t 28 a b s)
  have other := add_other ops t 28 u a b s hu
  exact ⟨(partial_other t u _ _ _ _ hu).trans other.1, (congrFun h.2.2.1 u).trans other.2⟩

theorem first_last_good (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (he : (s.epochs t).block = 0) (good : ∀ a ∈ s.trace, Good a) :
    ∀ access ∈ (firstLastAfter ops t a b s).trace, Good access :=
  partial_good t _ _ _ _ rfl rfl he good

#print axioms partial_lane
#print axioms partial_fields
#print axioms partial_value
#print axioms partial_good
#print axioms first_last_lane
#print axioms first_last_fields
#print axioms first_last_other
#print axioms first_last_good
end LarkNativeFlashInferRmsNorm
