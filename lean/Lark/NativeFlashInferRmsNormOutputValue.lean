import Lark.NativeFlashInferRmsNormOutputEntry

/-! Output values and exact effects of one source component. Input and weight
are read-only globals with explicit half conversions; the literal zero in the
weight add and final half cast retain the source order.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowInput (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.fromHalf (input 1 (address row col))

def outputWeighted (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) (inverse : α) : α :=
  ops.mul (ops.mul (rowInput ops input row col) inverse)
    (ops.add (ops.literal 0 1) (ops.fromHalf (input 2 col)))

def outputComponent (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row col
  let x := rowInput ops input row col
  let w := ops.fromHalf (input 2 col)
  let s := advance s t 55
  let s := setIndex s t 10 (col : Int) 56
  let s := setIndex s t 11 (offset : Int) 57
  let s := setReg (record s t (globalCell 1 offset) false) t 8 x 58
  let s := setReg (record s t (globalCell 2 col) false) t 9 w 59
  let s := setReg s t 10 (ops.add (ops.literal 0 1) w) 60
  let s := setReg s t 11 (ops.mul x inverse) 61
  let s := setReg s t 12 (outputWeighted ops input row col inverse) 62
  let s := written t 63 (globalCell 0 offset) (ops.toHalf (outputWeighted ops input row col inverse)) s
  let s := setIndex s t 9 ((component + 1 : Nat) : Int) 64
  advance s t 54

theorem output_component_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) (l : Location) :
    (outputComponent ops input row tid iteration component t inverse s).memory l =
      if l = globalCell 0 (address row (column tid iteration component))
      then some (ops.toHalf (outputWeighted ops input row (column tid iteration component) inverse)) else s.memory l := rfl

theorem output_component_value (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row tid iteration component t inverse s).memory
      (globalCell 0 (address row (column tid iteration component))) =
      some (ops.toHalf (outputWeighted ops input row (column tid iteration component) inverse)) := by
  simp only [output_component_memory, ↓reduceIte]

theorem output_component_reads (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (reads : OutputReads ops input row s) :
    OutputReads ops input row (outputComponent ops input row tid iteration component t inverse s) := by
  intro col hc
  simpa [output_component_memory, globalCell] using reads col hc

theorem output_component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row tid iteration component t inverse s).pc t = 54 ∧
    (outputComponent ops input row tid iteration component t inverse s).indices t 0 = s.indices t 0 ∧
    (outputComponent ops input row tid iteration component t inverse s).indices t 1 = s.indices t 1 ∧
    (outputComponent ops input row tid iteration component t inverse s).indices t 8 = s.indices t 8 ∧
    (outputComponent ops input row tid iteration component t inverse s).indices t 9 = some ((component + 1 : Nat) : Int) ∧
    (outputComponent ops input row tid iteration component t inverse s).regs t 7 = s.regs t 7 := by
  simp [outputComponent, setReg, setIndex, written, record, advance]

theorem output_component_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputComponent ops input row tid iteration component t inverse s).pc u = s.pc u ∧
    (outputComponent ops input row tid iteration component t inverse s).indices u = s.indices u ∧
    (outputComponent ops input row tid iteration component t inverse s).regs u = s.regs u := by
  simp [outputComponent, setReg, setIndex, written, record, advance, hu]

theorem output_component_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row tid iteration component t inverse s).epochs = s.epochs := rfl

theorem output_component_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row tid iteration component t inverse s).trace =
      ⟨t, globalCell 0 (address row (column tid iteration component)), true, s.epochs t⟩ ::
      ⟨t, globalCell 2 (column tid iteration component), false, s.epochs t⟩ ::
      ⟨t, globalCell 1 (address row (column tid iteration component)), false, s.epochs t⟩ :: s.trace := rfl

theorem output_component_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) (he : t = row * 1024 + tid)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (outputComponent ops input row tid iteration component t inverse s).trace, Good a := by
  have hw := he.trans (address_writer row tid iteration component ht hi hc).symm
  intro a ha
  simp only [output_component_trace, List.mem_cons] at ha
  rcases ha with rfl | rfl | rfl | ha
  · exact Good.output rfl rfl rfl hw
  · exact Good.input rfl rfl (Or.inr rfl) rfl
  · exact Good.input rfl rfl (Or.inl rfl) rfl
  · exact good a ha

#print axioms output_component_memory
#print axioms output_component_value
#print axioms output_component_reads
#print axioms output_component_fields
#print axioms output_component_other
#print axioms output_component_epochs
#print axioms output_component_trace
#print axioms output_component_good
end LarkNativeFlashInferRmsNorm
