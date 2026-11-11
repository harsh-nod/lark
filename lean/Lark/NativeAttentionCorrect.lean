import Lark.NativeAttentionWholeLaunch

/-! Whole-launch correctness against the source-ordered online recurrence.
Canonical dense-real equality and floating-point error bounds are separate obligations. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

theorem source_extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv : ∀ i, i < p.groups * 32768 → s.memory (globalCell 0 i) = some (outputValue ops input i)) :
    extract (layout p) s = some (sourceSpec p ops input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range (p.groups * 32768)).map (fun i => (0, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rewrite [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.groups * 32768))
    (fun i => s.memory (globalCell 0 i)) (outputValue ops input) (by intro i hi; exact hv i (List.mem_range.mp hi))

theorem grid_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout p) (gridState p ops input (initial (layout p) input outside)) = some (sourceSpec p ops input) :=
  source_extract_of_values p ops input _ (grid_value p ops input outside)

/-- The original scalar machine's complete `Correct` relation for the unchanged
native program, geometry and fuel, against its explicit online-recurrence spec. -/
theorem source_order_correct (p : Shape) (ops : Ops α) :
    Correct ops (layout p) (geometry p) fuel program (sourceSpec p ops) := by
  intro input outside
  exact ⟨gridState p ops input (initial (layout p) input outside), grid_run p ops input outside,
    grid_race_free p ops input outside, grid_extract p ops input outside⟩

#print axioms source_extract_of_values
#print axioms grid_extract
#print axioms source_order_correct
end LarkNativeAttention
