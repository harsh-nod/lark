import Lark.NativeRmsNormOutBarrier

/-! Actual shared-scale load and vector-index setup after the second barrier. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outLoaded (t row : Nat) (value : α) (s : State α) : State α :=
  setReg (record s t (scaleSlot row) false) t 4 value 57

def outEntered (t row tid : Nat) (value : α) (s : State α) : State α :=
  setIndex (outLoaded t row value s) t 7 (tid : Int) 58

theorem out_load_code : program[56]? = some (.scalar (.assign 4 (.load .shared 1 (.const 0)))) := by decide
theorem out_index_code : program[57]? = some (.scalar (.index 7 (.ivar 1))) := by decide

theorem output_entry_eq (p : Shape) (ops : Ops α) (t row tid extra : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (hi : s.indices t 1 = some (tid : Int))
    (hx : s.memory (scaleSlot row) = some value) (hp : s.pc t = 56) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 2) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outEntered t row tid value s) := by
  have hl : location (layout p) (geometry p) t .shared 1 0 false = some (scaleSlot row) := by
    simp [location, layout, geometry, scaleSlot, hr]
  have he : evalExpr ops (layout p) (geometry p) t (.load .shared 1 (.const 0)) s =
      some (value, record s t (scaleSlot row) false) := by
    simp only [evalExpr, show evalIndex (geometry p) t s (.const 0) = some 0 from rfl,
      bind, pure, Option.bind, hl, hx]
  have h1 : execute ops (layout p) (geometry p) t (.assign 4 (.load .shared 1 (.const 0))) s =
      some (outLoaded t row value s) := by
    simp only [execute, he, hp, bind, pure, Option.bind]
    rfl
  have h2 := execute_index_of ops (layout p) (geometry p) t 7 58 (.ivar 1)
    (outLoaded t row value s) (tid : Int) hi (by simp [outLoaded, setReg, advance])
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, hp, out_load_code]) (by simpa only [hp] using out_load_code) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, outLoaded, setReg, advance, out_index_code])
    (by simpa only [outLoaded, setReg, advance, ↓reduceIte] using out_index_code) h2]
  rfl

theorem output_entry_preserves (t row tid : Nat) (value : α) (s : State α) :
    (outEntered t row tid value s).memory = s.memory ∧
    (outEntered t row tid value s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem output_entry_fields (t row tid : Nat) (value : α) (s : State α) :
    (outEntered t row tid value s).pc t = 58 ∧
    (outEntered t row tid value s).indices t 0 = s.indices t 0 ∧
    (outEntered t row tid value s).indices t 7 = some (tid : Int) ∧
    (outEntered t row tid value s).regs t 4 = some value := by
  simp [outEntered, outLoaded, setReg, setIndex, advance, record]

theorem output_entry_other (t u row tid : Nat) (value : α) (s : State α) (hu : u ≠ t) :
    (outEntered t row tid value s).pc u = s.pc u ∧
    (outEntered t row tid value s).indices u = s.indices u ∧
    (outEntered t row tid value s).regs u = s.regs u := by
  simp [outEntered, outLoaded, setReg, setIndex, advance, record, hu]

theorem output_entry_good (p : Shape) (t row tid : Nat) (value : α) (s : State α)
    (hr : t / 1024 = row) (he : (s.epochs t).block = 2)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outEntered t row tid value s).trace, LarkReductionFootprint.Good (traversal p) 0 a := by
  intro a ha
  change a ∈ ⟨t, scaleSlot row, false, s.epochs t⟩ :: s.trace at ha
  rcases List.mem_cons.mp ha with h | h
  · subst a
    exact .scaleLoad rfl hr.symm rfl rfl he rfl
  · exact good a h

#print axioms output_entry_eq
#print axioms output_entry_good
end LarkNativeRmsNorm
