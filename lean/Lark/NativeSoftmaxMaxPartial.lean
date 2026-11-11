import Lark.NativeSoftmaxMaxStages

/-! Actual final downward maximum, logical-lane-zero partial store and first barrier.
Each native wave has two distinct partial writers, one per logical32 group.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def written (t pc : Nat) (loc : Location) (value : α) (s : State α) : State α :=
  advance { record s t loc true with
    memory := fun l => if l = loc then some value else s.memory l } t pc

theorem written_memory (t pc : Nat) (loc l : Location) (value : α) (s : State α) :
    (written t pc loc value s).memory l = if l = loc then some value else s.memory l := rfl

theorem first_barrier (guarded : Bool) :
    (program guarded)[32]? = some (.scalar (.barrier .block)) := by cases guarded <;> decide

def partialCell (t warp : Nat) : Location := ⟨.shared, t / 1024, 0, warp⟩
def partialWritten (t warp : Nat) (value : α) (s : State α) : State α :=
  written t 32 (partialCell t warp) value s
def partialAfter (t lane warp : Nat) (value : α) (s : State α) : State α :=
  if lane = 0 then partialWritten t warp value (advance s t 31) else advance s t 32

theorem partial_branch_code (guarded : Bool) :
    (program guarded)[30]? = some (.scalar (.branch (.eq (.ivar 3) (.const 0)) 32)) := by cases guarded <;> decide
theorem partial_store_code (guarded : Bool) :
    (program guarded)[31]? = some (.scalar (.store .shared 0 (.ivar 2) (.reg 0))) := by cases guarded <;> decide

theorem partial_location (p : Shape) (t warp : Nat) (hw : warp < 32) :
    location (layout p) (geometry p) t .shared 0 (warp : Int) true = some (partialCell t warp) := by
  simp [location, layout, geometry, partialCell, show ¬ (warp : Int) < 0 by omega, hw]

theorem partial_store_eq (p : Shape) (ops : Ops α) (t warp : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi : s.indices t 2 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t = 31) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.ivar 2) (.reg 0)) s =
      some (partialWritten t warp value s) := by
  simp [execute, evalIndex, hi, partial_location p t warp hw, evalExpr, ha, hp, partialWritten, written, record]

theorem partial_lane (p : Shape) (guarded : Bool) (ops : Ops α) (t lane warp extra : Nat) (value : α) (s : State α)
    (hw : warp < 32) (hi2 : s.indices t 3 = some (lane : Int))
    (hi3 : s.indices t 2 = some (warp : Int)) (ha : s.regs t 0 = some value) (hp : s.pc t = 30) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra + 3) s =
      some (partialAfter t lane warp value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some (decide (lane = 0)) := by
    simp [evalPredicate, evalIndex, hi2, int32] <;> omega
  by_cases hl : lane = 0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some true := by simpa [hl] using heq
    let s1 := advance s t 31
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 32) s = some s1 := by
      simp [execute, hg, hp, s1]
    have e2 := partial_store_eq p ops t warp value s1 hw hi3 ha (by simp [s1, advance])
    rewrite [scalar_step p guarded ops t 30 _ _ s s1 (partial_branch_code guarded) hp e1]
    rewrite [scalar_step p guarded ops t 31 _ _ s1 _ (partial_store_code guarded) (by simp [s1, advance]) e2]
    have hcut : LarkCollective.parked (program guarded) (partialWritten t warp value s1) t = some .block := by
      simp only [LarkCollective.parked, partialWritten, written, advance, ↓reduceIte]
      rewrite [first_barrier guarded]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0)) = some false := by simpa [hl] using heq
    have e1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 32) s =
        some (advance s t 32) := by simp [execute, hg]
    rewrite [scalar_step p guarded ops t 30 _ _ s _ (partial_branch_code guarded) hp e1]
    have hcut : LarkCollective.parked (program guarded) (advance s t 32) t = some .block := by
      simp only [LarkCollective.parked, advance, ↓reduceIte]
      rewrite [first_barrier guarded]
      rfl
    rewrite [LarkCollective.runLane, hcut]
    simp only [partialAfter, hl, ↓reduceIte]

theorem partial_fields (t lane warp : Nat) (value : α) (s : State α) :
    (partialAfter t lane warp value s).pc t = 32 ∧
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
    · apply Good.partialStore rfl rfl (by change 0 < 2; decide)
      · exact hw
      · change (t % 1024) % 32 = 0
        omega
      · simpa only [partialCell,Nat.mul_zero] using he
      · rfl
    · exact good a ha
  · simpa only [partialAfter, hz, ↓reduceIte, advance] using good

def firstLastAfter (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  partialAfter t ((t % 1024) % 32) ((t % 1024) / 32) (ops.max a b) (combineAfter ops t 29 a b s)

theorem first_last_lane (p : Shape) (guarded : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (hi : MaxNativeIndices t s) (ha : s.regs t 0 = some a) (hb : s.regs t 2 = some b) (hp : s.pc t = 29) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s =
      some (firstLastAfter ops t a b s) := by
  rewrite [show fuel.lane = 4095 + 1 by decide,
    combine_eq p guarded ops t 29 4095 a b s hp ha hb (by cases guarded <;> decide)]
  apply partial_lane p guarded ops t ((t % 1024) % 32) ((t % 1024) / 32) 4092 (ops.max a b) (combineAfter ops t 29 a b s)
    (by omega) hi.2.2.2 hi.2.2.1
  · simp [combineAfter, LarkReduction.setReg, advance]
  · simp [combineAfter, LarkReduction.setReg, advance]

theorem first_last_fields (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (firstLastAfter ops t a b s).pc t = 32 ∧
    (firstLastAfter ops t a b s).regs t 0 = some (ops.max a b) ∧
    (firstLastAfter ops t a b s).indices = s.indices ∧
    (firstLastAfter ops t a b s).epochs = s.epochs := by
  have h := partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.max a b) (combineAfter ops t 29 a b s)
  refine ⟨h.1, ?_, h.2.1, h.2.2.2⟩
  rewrite [show (firstLastAfter ops t a b s).regs = (combineAfter ops t 29 a b s).regs from h.2.2.1]
  simp [combineAfter, LarkReduction.setReg, advance]

theorem first_last_other (ops : Ops α) (t u : Nat) (a b : α) (s : State α) (hu : u ≠ t) :
    (firstLastAfter ops t a b s).pc u = s.pc u ∧
    (firstLastAfter ops t a b s).regs u = s.regs u := by
  have h := partial_fields t ((t % 1024) % 32) ((t % 1024) / 32) (ops.max a b) (combineAfter ops t 29 a b s)
  have other := combine_other ops t 29 u a b s hu
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
#print axioms written_memory
#print axioms first_barrier
#print axioms partial_branch_code
#print axioms partial_store_code
#print axioms partial_location
#print axioms partial_store_eq
#print axioms partial_other
#print axioms partial_memory_other
end LarkNativeSoftmax
