import Lark.NativeFusedRmsNormBarrier

/-! Actual source PC36 entry to the logical32 block reduction. Active threads
read their own partial slots; all other threads stop at the second barrier.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setReg int32_cast)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def partialSlot (row slot : Nat) : Location := ⟨.shared, row, 0, slot⟩
def midLoaded (t row tid : Nat) (value : α) (s : State α) : State α :=
  setReg (record (advance s t 37) t (partialSlot row tid) false) t 0 value 38
def midEntered (t row tid : Nat) (value : α) (s : State α) : State α :=
  if tid < 32 then midLoaded t row tid value s else advance s t 50

theorem mid_branch_code : program[36]? = some (.scalar (.branch (.lt (.ivar 1) (.const 32)) 50)) := by decide
theorem mid_load_code : program[37]? = some (.scalar (.assign 0 (.load .shared 0 (.ivar 1)))) := by decide
theorem mid_shuffle_code : program[38]? = some (.shuffle .xor 1 0 (.const 16) 32) := by decide

theorem partial_slot_location (p : Shape) (t row tid : Nat) (hr : t / 1024 = row) (ht : tid < 32) :
    location (layout p) (geometry p) t .shared 0 (tid : Int) false = some (partialSlot row tid) := by
  simp [location, layout, geometry, partialSlot, hr, show ¬ (tid : Int) < 0 by omega, ht]

theorem mid_enter_active (p : Shape) (ops : Ops α) (t row tid : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (ht : tid < 32) (hi : s.indices t 1 = some (tid : Int))
    (hx : s.memory (partialSlot row tid) = some value) (hp : s.pc t = 36) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (midLoaded t row tid value s) := by
  let s1 := advance s t 37
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 1) (.const 32)
    (tid : Int) 32 hi (int32_cast 32 (by decide)) (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 32)) 50) s = some s1 := by
    simp [execute, hg, hp, s1]
  have he : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.ivar 1)) s1 =
      some (value, record s1 t (partialSlot row tid) false) := by
    simp only [evalExpr, evalIndex, show s1.indices t 1 = some (tid : Int) from hi,
      bind, pure, Option.bind, partial_slot_location p t row tid hr ht]
    rewrite [show s1.memory (partialSlot row tid) = some value from hx]
    rfl
  have e2 : execute ops (layout p) (geometry p) t (.assign 0 (.load .shared 0 (.ivar 1))) s1 =
      some (midLoaded t row tid value s) := by
    simp only [execute, he, bind, pure, Option.bind]
    rewrite [show s1.pc t + 1 = 38 by simp [s1, advance]]
    rfl
  rewrite [show fuel.lane = (510 + 1) + 1 by decide,
    scalar_step p ops t 36 _ _ s s1 mid_branch_code hp e1,
    scalar_step p ops t 37 _ _ s1 _ mid_load_code (by simp [s1, advance]) e2]
  have hcut : LarkCollective.parked program (midLoaded t row tid value s) t = some .shuffle := by
    simp only [LarkCollective.parked, midLoaded, setReg, advance, ↓reduceIte, mid_shuffle_code]
  rewrite [LarkCollective.runLane, hcut]
  rfl

theorem mid_enter_inactive (p : Shape) (ops : Ops α) (t tid : Nat) (s : State α)
    (ht : ¬ tid < 32) (hi : s.indices t 1 = some (tid : Int)) (hp : s.pc t = 36) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some (advance s t 50) := by
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.ivar 1) (.const 32)
    (tid : Int) 32 hi (int32_cast 32 (by decide)) (by omega)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 32)) 50) s =
      some (advance s t 50) := by simp [execute, hg]
  rewrite [show fuel.lane = 511 + 1 by decide, scalar_step p ops t 36 _ _ s _ mid_branch_code hp he]
  have hcut : LarkCollective.parked program (advance s t 50) t = some .block := by
    simp only [LarkCollective.parked, advance, ↓reduceIte, second_barrier]
    rfl
  rewrite [LarkCollective.runLane, hcut]
  rfl

theorem mid_entered_run (p : Shape) (ops : Ops α) (t row tid : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (hi : s.indices t 1 = some (tid : Int))
    (hx : tid < 32 → s.memory (partialSlot row tid) = some value) (hp : s.pc t = 36) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s = some (midEntered t row tid value s) := by
  by_cases ht : tid < 32
  · simpa only [midEntered, ht, ↓reduceIte] using mid_enter_active p ops t row tid value s hr ht hi (hx ht) hp
  · simpa only [midEntered, ht, ↓reduceIte] using mid_enter_inactive p ops t tid s ht hi hp

theorem mid_entry_preserves (t row tid : Nat) (value : α) (s : State α) :
    (midEntered t row tid value s).memory = s.memory ∧
    (midEntered t row tid value s).indices = s.indices ∧ (midEntered t row tid value s).epochs = s.epochs := by
  unfold midEntered
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem mid_entry_other (t u row tid : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (midEntered t row tid value s).pc u = s.pc u ∧ (midEntered t row tid value s).regs u = s.regs u := by
  unfold midEntered
  split <;> simp [midLoaded, setReg, advance, record, hu]

theorem mid_entry_pc (t row tid : Nat) (value : α) (s : State α) :
    (midEntered t row tid value s).pc t = if tid < 32 then 38 else 50 := by
  unfold midEntered
  split <;> simp [midLoaded, setReg, advance, *]

theorem mid_entry_acc (t row tid : Nat) (value : α) (s : State α) (ht : tid < 32) :
    (midEntered t row tid value s).regs t 0 = some value := by
  simp [midEntered, ht, midLoaded, setReg, advance, record]

theorem mid_entry_good (t row tid : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (hi : t % 1024 = tid) (he : (s.epochs t).block = 1)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (midEntered t row tid value s).trace, Good a := by
  by_cases ht : tid < 32
  · intro a ha
    simp only [midEntered, ht, ↓reduceIte, midLoaded, setReg, advance, record, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Good.partialRead rfl hr.symm rfl hi he rfl
    · exact good a ha
  · simpa only [midEntered, ht, ↓reduceIte, advance] using good

#print axioms mid_enter_active
#print axioms mid_enter_inactive
#print axioms mid_entered_run
#print axioms mid_entry_preserves
#print axioms mid_entry_other
#print axioms mid_entry_good
end LarkNativeFusedRmsNorm
