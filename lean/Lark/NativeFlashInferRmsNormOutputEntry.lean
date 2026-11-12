import Lark.NativeFlashInferRmsNormOutBarrier

/-! Actual normalization setup after both barriers. Division, epsilon addition
and reciprocal square root keep the source order for arbitrary operations.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex execute_pure_of execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputInverse (ops : Ops α) (total : α) : α :=
  ops.rsqrt (ops.add (ops.div total (ops.literal 16384 1)) (ops.literal 1 100000))

def outputEntered (ops : Ops α) (t row : Nat) (total : α) (s : State α) : State α :=
  let s := setReg (record s t (partialSlot row 0) false) t 4 total 48
  let s := setReg s t 5 (ops.div total (ops.literal 16384 1)) 49
  let s := setReg s t 6 (ops.add (ops.div total (ops.literal 16384 1)) (ops.literal 1 100000)) 50
  let s := setReg s t 7 (outputInverse ops total) 51
  setIndex s t 8 0 52

theorem output_entry_eq (p : Shape) (ops : Ops α) (t row extra : Nat) (total : α) (s : State α)
    (hr : t / 1024 = row) (hp : s.pc t = 47)
    (hm : s.memory (partialSlot row 0) = some total) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 5) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputEntered ops t row total s) := by
  let s1 := setReg (record s t (partialSlot row 0) false) t 4 total 48
  let mean := ops.div total (ops.literal 16384 1)
  let s2 := setReg s1 t 5 mean 49
  let shifted := ops.add mean (ops.literal 1 100000)
  let s3 := setReg s2 t 6 shifted 50
  let s4 := setReg s3 t 7 (outputInverse ops total) 51
  have hl : location (layout p) (geometry p) t .shared 0 0 false = some (partialSlot row 0) :=
    partial_slot_location p t row 0 hr (by decide)
  have he1 : evalExpr ops (layout p) (geometry p) t (.load .shared 0 (.const 0)) s =
      some (total, record s t (partialSlot row 0) false) := by
    simp only [evalExpr, show evalIndex (geometry p) t s (.const 0) = some 0 from rfl,
      hl, hm, bind, pure, Option.bind]
  have e1 : execute ops (layout p) (geometry p) t (.assign 4 (.load .shared 0 (.const 0))) s = some s1 := by
    simp only [execute, he1, hp, bind, pure, Option.bind]
    rfl
  have e2 := execute_pure_of ops (layout p) (geometry p) t 5 49
    (.bin .div (.reg 4) (.lit 16384 1)) s1 mean
    (by simp [evalExpr, applyBinary, s1, mean, setReg, record, advance])
    (by simp [s1, setReg, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 := execute_pure_of ops (layout p) (geometry p) t 6 50
    (.bin .add (.reg 5) (.lit 1 100000)) s2 shifted
    (by simp [evalExpr, applyBinary, s2, shifted, setReg, advance])
    (by simp [s2, setReg, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_pure_of ops (layout p) (geometry p) t 7 51
    (.un .rsqrt (.reg 6)) s3 (outputInverse ops total)
    (by simp [evalExpr, applyUnary, s3, shifted, mean, outputInverse, setReg, advance])
    (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 := execute_index_of ops (layout p) (geometry p) t 8 52 (.const 0) s4 0 rfl
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some (outputEntered ops t row total s) at e5
  rewrite [scalar_step p ops t 47 _ _ s s1 (by decide) hp e1]
  rewrite [scalar_step p ops t 48 _ _ s1 s2 (by decide) (by simp [s1, setReg, advance]) e2]
  rewrite [scalar_step p ops t 49 _ _ s2 s3 (by decide) (by simp [s2, setReg, advance]) e3]
  rewrite [scalar_step p ops t 50 _ _ s3 s4 (by decide) (by simp [s3, setReg, advance]) e4]
  rewrite [scalar_step p ops t 51 _ _ s4 _ (by decide) (by simp [s4, setReg, advance]) e5]
  rfl

theorem output_entry_preserves (ops : Ops α) (t row : Nat) (total : α) (s : State α) :
    (outputEntered ops t row total s).memory = s.memory ∧
    (outputEntered ops t row total s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem output_entry_fields (ops : Ops α) (t row : Nat) (total : α) (s : State α) :
    (outputEntered ops t row total s).pc t = 52 ∧
    (outputEntered ops t row total s).indices t 0 = s.indices t 0 ∧
    (outputEntered ops t row total s).indices t 1 = s.indices t 1 ∧
    (outputEntered ops t row total s).indices t 8 = some 0 ∧
    (outputEntered ops t row total s).regs t 7 = some (outputInverse ops total) := by
  simp [outputEntered, setReg, setIndex, record, advance]

theorem output_entry_other (ops : Ops α) (t u row : Nat) (total : α) (s : State α) (hu : u ≠ t) :
    (outputEntered ops t row total s).pc u = s.pc u ∧
    (outputEntered ops t row total s).indices u = s.indices u ∧
    (outputEntered ops t row total s).regs u = s.regs u := by
  simp [outputEntered, setReg, setIndex, record, advance, hu]

theorem output_entry_good (ops : Ops α) (t row : Nat) (total : α) (s : State α)
    (hr : t / 1024 = row) (he : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (outputEntered ops t row total s).trace, Good a := by
  intro a ha
  change a ∈ ⟨t, partialSlot row 0, false, s.epochs t⟩ :: s.trace at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.broadcast rfl hr.symm rfl rfl he rfl
  · exact good a ha

def OutputReads (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ col, col < 16384 →
    s.memory (globalCell 1 (address row col)) = some (input 1 (address row col)) ∧
    s.memory (globalCell 2 col) = some (input 2 col)

theorem out_ready_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat)
    (s : State α) (ready : OutReady p ops input row s) : OutputReads ops input row s :=
  fun col hc => ⟨ready.cells col hc, ready.weights col hc⟩

#print axioms output_entry_eq
#print axioms output_entry_preserves
#print axioms output_entry_fields
#print axioms output_entry_other
#print axioms output_entry_good
#print axioms out_ready_reads
end LarkNativeFlashInferRmsNorm
