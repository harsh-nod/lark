import Lark.NativeRmsNormBarrier

/-! Actual PC 39 entry to the logical-16 scale phase. Active lanes load the
shared partials; all other native threads stop at the second block barrier.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setReg int32_cast)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def partialSlot (row slot : Nat) : Location := ⟨.shared, row, 0, slot⟩

def midLoaded (t row lane : Nat) (value : α) (s : State α) : State α :=
  setReg (record (advance s t 40) t (partialSlot row lane) false) t 0 value 41

def midEntered (t row tid lane : Nat) (value : α) (s : State α) : State α :=
  if tid < 16 then midLoaded t row lane value s else advance s t 55

theorem mid_branch_code : program[39]? = some (.scalar (.branch (.lt (.ivar 1) (.const 16)) 55)) := by decide
theorem mid_load_code : program[40]? = some (.scalar (.assign 0 (.load .shared 0 (.ivar 2)))) := by decide

theorem partial_slot_location (p : Shape) (t row lane : Nat) (hr : t / 1024 = row) (hl : lane < 16) :
    location (layout p) (geometry p) t .shared 0 (lane : Int) false = some (partialSlot row lane) := by
  simp [location, layout, geometry, partialSlot, hr, show ¬ (lane : Int) < 0 by omega, hl]

theorem mid_enter_active (p : Shape) (ops : Ops α) (t row tid lane : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (ht : tid < 16) (hl : lane < 16)
    (hi1 : s.indices t 1 = some (tid : Int)) (hi2 : s.indices t 2 = some (lane : Int))
    (hx : s.memory (partialSlot row lane) = some value) (hp : s.pc t = 39) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (midLoaded t row lane value s) := by
  let s1 := advance s t 40
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 1) (.const 16)
    (tid : Int) 16 hi1 (int32_cast 16 (by decide)) (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 16)) 55) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have he : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.ivar 2)) s1 =
      some (value, record s1 t (partialSlot row lane) false) := by
    simp only [evalExpr, evalIndex, show s1.indices t 2 = some (lane : Int) from hi2,
      bind, pure, Option.bind, partial_slot_location p t row lane hr hl]
    rewrite [show s1.memory (partialSlot row lane) = some value from hx]
    rfl
  have h2 : execute ops (layout p) (geometry p) t (.assign 0 (.load .shared 0 (.ivar 2))) s1 =
      some (midLoaded t row lane value s) := by
    simp only [execute, he, bind, pure, Option.bind]
    rewrite [show s1.pc t + 1 = 41 by simp [s1, advance]]
    rfl
  rewrite [show fuel.lane = (254 + 1) + 1 by decide,
    scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, mid_branch_code]) (by simpa only [hp] using mid_branch_code) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, s1, advance, mid_load_code])
    (by simpa only [s1, advance, ↓reduceIte] using mid_load_code) h2]
  have hcut : LarkCollective.parked program (midLoaded t row lane value s) t = some .shuffle := by
    unfold LarkCollective.parked
    simp only [midLoaded, setReg, advance, ↓reduceIte]
    rewrite [final_shuffle 0 (by decide)]
    rfl
  rewrite [LarkCollective.runLane, hcut]
  rfl

theorem mid_enter_inactive (p : Shape) (ops : Ops α) (t tid : Nat) (s : State α)
    (ht : ¬ tid < 16) (hi : s.indices t 1 = some (tid : Int)) (hp : s.pc t = 39) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some (advance s t 55) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 1) (.const 16)
    (tid : Int) 16 hi (int32_cast 16 (by decide)) (by omega)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 16)) 55) s =
      some (advance s t 55) := by
    simp only [execute, hg, bind, pure, Option.bind]
    rfl
  rewrite [show fuel.lane = 255 + 1 by decide,
    scalar_step ops _ _ _ _ _ _ _ _
      (by simp [LarkCollective.parked, hp, mid_branch_code]) (by simpa only [hp] using mid_branch_code) he]
  have hcut : LarkCollective.parked program (advance s t 55) t = some .block := by
    unfold LarkCollective.parked
    simp only [advance, ↓reduceIte]
    rewrite [second_barrier]
    rfl
  rewrite [LarkCollective.runLane, hcut]
  rfl

theorem mid_entry_preserves (t row tid lane : Nat) (value : α) (s : State α) :
    (midEntered t row tid lane value s).memory = s.memory ∧
    (midEntered t row tid lane value s).indices = s.indices ∧
    (midEntered t row tid lane value s).epochs = s.epochs := by
  unfold midEntered
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem mid_entered_run (p : Shape) (ops : Ops α) (t row tid lane : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (hl : tid < 16 → lane < 16)
    (hi1 : s.indices t 1 = some (tid : Int)) (hi2 : s.indices t 2 = some (lane : Int))
    (hx : tid < 16 → s.memory (partialSlot row lane) = some value) (hp : s.pc t = 39) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (midEntered t row tid lane value s) := by
  by_cases ht : tid < 16
  · simp only [midEntered, ht, ↓reduceIte]
    exact mid_enter_active p ops t row tid lane value s hr ht (hl ht) hi1 hi2 (hx ht) hp
  · simp only [midEntered, ht, ↓reduceIte]
    exact mid_enter_inactive p ops t tid s ht hi1 hp

theorem mid_entry_acc (t row tid lane : Nat) (value : α) (s : State α) (ht : tid < 16) :
    (midEntered t row tid lane value s).regs t 0 = some value := by
  simp [midEntered, ht, midLoaded, setReg, advance, record]

theorem mid_entry_other (t u row tid lane : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (midEntered t row tid lane value s).pc u = s.pc u ∧
    (midEntered t row tid lane value s).regs u = s.regs u := by
  unfold midEntered
  split <;> simp [midLoaded, setReg, advance, record, hu]

theorem mid_entry_pc (t row tid lane : Nat) (value : α) (s : State α) :
    (midEntered t row tid lane value s).pc t = if tid < 16 then 41 else 55 := by
  unfold midEntered
  split <;> simp [midLoaded, setReg, advance, *]

theorem mid_entry_good (p : Shape) (t row tid lane : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (he : (s.epochs t).block = 1)
    (good : ∀ access ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 access) :
    ∀ access ∈ (midEntered t row tid lane value s).trace, LarkReductionFootprint.Good (traversal p) 0 access := by
  by_cases ht : tid < 16
  · intro access ha
    simp only [midEntered, ht, ↓reduceIte, midLoaded, setReg, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · apply LarkReductionFootprint.Good.partialLoad
      · rfl
      · exact hr.symm
      · rfl
      · exact he
      · rfl
    · exact good access ha
  · simpa only [midEntered, ht, ↓reduceIte, advance] using good

#print axioms mid_enter_active
#print axioms mid_enter_inactive
#print axioms mid_entry_good
end LarkNativeRmsNorm
