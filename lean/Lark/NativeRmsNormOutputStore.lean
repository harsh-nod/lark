import Lark.NativeRmsNormOutputEntry

/-! Actual output store, bounds, unique writer and read-only-input frame. -/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputWritten (t offset : Nat) (value : α) (s : State α) : State α :=
  let s := record s t (globalCell 0 offset) true
  advance { s with memory := fun l => if l = globalCell 0 offset then some value else s.memory l } t 66

theorem output_location (p : Shape) (t row vector component : Nat)
    (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8) :
    location (layout p) (geometry p) t .global 0 (scalarAddress row vector component : Nat) true =
      some (globalCell 0 (scalarAddress row vector component)) := by
  have hb := scalar_address_bound p row vector component hr hv hc
  have hn : ¬ ((scalarAddress row vector component : Nat) : Int) < 0 := by omega
  simp [location, layout, globalCell, hn, hb, show (Role.output == Role.input) = false by decide]

theorem output_store_eq (p : Shape) (ops : Ops α) (t row vector component : Nat)
    (value : α) (s : State α) (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8)
    (hi0 : s.indices t 0 = some (row : Int)) (hi7 : s.indices t 7 = some (vector : Int))
    (hi8 : s.indices t 8 = some (component : Int)) (hx : s.regs t 8 = some value) (hp : s.pc t = 65) :
    execute ops (layout p) (geometry p) t
      (.store .global 0 (rowIndex 7 8) (.un .toHalf (.reg 8))) s =
      some (outputWritten t (scalarAddress row vector component) (ops.toHalf value) s) := by
  have he := eval_row_address p (geometry p) t 7 8 row vector component s hi0 hi7 hi8 hr hv hc
  have hx' : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 8)) s =
      some (ops.toHalf value, s) := by simp [evalExpr, applyUnary, hx]
  simp only [execute, he, output_location p t row vector component hr hv hc,
    hx', bind, pure, Option.bind, hp]
  rfl

theorem output_writer (p : Shape) (row vector component : Nat) (hv : vector < 2048) (hc : component < 8) :
    LarkVectorStride.writer (traversal p) (scalarAddress row vector component) = row * 1024 + vector % 1024 := by
  have hd := Nat.div_add_mod vector 1024
  have he : vector % 1024 + vector / 1024 * 1024 = vector := by omega
  have hl : vector % 1024 < (traversal p).block := Nat.mod_lt _ (by decide)
  have hvec : LarkVectorStride.vectors (traversal p) = 2048 :=
    Nat.div_eq_of_eq_mul_left (by decide : 0 < 8) (by decide : 16384 = 2048 * 8)
  have hv' : vector % 1024 + vector / 1024 * (traversal p).block < LarkVectorStride.vectors (traversal p) := by
    rewrite [hvec]
    change vector % 1024 + vector / 1024 * 1024 < 2048
    omega
  have h := LarkVectorStride.address_writer (traversal p) row (vector % 1024) (vector / 1024) component hl hv' hc
  simpa only [LarkVectorStride.address, LarkVectorStride.column, traversal, he,
    scalarAddress, Nat.add_assoc] using h

theorem output_written_memory_other (t offset : Nat) (value : α) (s : State α) (l : Location)
    (hl : l ≠ globalCell 0 offset) : (outputWritten t offset value s).memory l = s.memory l := by
  simp [outputWritten, advance, record, hl]

theorem output_written_reads (p : Shape) (input : Nat → Nat → α) (t offset : Nat) (value : α)
    (s : State α) (reads : Reads p input s) : Reads p input (outputWritten t offset value s) := by
  constructor
  · intro i hi
    exact (output_written_memory_other t offset value s (globalCell 1 i) (by simp [globalCell])).trans (reads.1 i hi)
  · intro i hi
    exact (output_written_memory_other t offset value s (globalCell 2 i) (by simp [globalCell])).trans (reads.2 i hi)

theorem output_written_good (p : Shape) (t row vector component : Nat) (value : α) (s : State α)
    (hv : vector < 2048) (hc : component < 8) (ht : t = row * 1024 + vector % 1024)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputWritten t (scalarAddress row vector component) value s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  intro a ha
  change a ∈ ⟨t, globalCell 0 (scalarAddress row vector component), true, s.epochs t⟩ :: s.trace at ha
  rcases List.mem_cons.mp ha with he | he
  · subst a
    exact .output rfl rfl rfl rfl (ht.trans (output_writer p row vector component hv hc).symm)
  · exact good a he

#print axioms output_store_eq
#print axioms output_writer
#print axioms output_written_good
end LarkNativeRmsNorm
