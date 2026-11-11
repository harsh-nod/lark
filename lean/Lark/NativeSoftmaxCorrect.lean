import Lark.NativeSoftmaxGridRun

/-! Repaired whole-launch correctness against the explicit source-ordered
normalization formula. The specification retains the source's max/sum order
and every half conversion. Canonical-real and IEEE reference bridges remain
separate obligations; no algebraic properties of arbitrary Ops are assumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sourceOutputValue (ops : Ops α) (input : Nat → Nat → α) (offset : Nat) : α :=
  normOutputValue ops input (offset/50257) (offset%50257)

def sourceOrderedSpec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows*50257)).map (sourceOutputValue ops input)

theorem source_ordered_spec_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) :
    (sourceOrderedSpec p ops input).length=p.rows*50257 := by simp [sourceOrderedSpec]

theorem source_extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv : ∀ offset, offset<p.rows*50257 → s.memory (globalCell 0 offset)=some (sourceOutputValue ops input offset)) :
    extract (layout p) s=some (sourceOrderedSpec p ops input) := by
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,List.flatMap_nil]
  simp only [List.map_cons,List.map_nil,show Role.input ≠ Role.output by decide,
    ↓reduceIte,List.nil_append,List.append_nil]
  change (((List.range (p.rows*50257)).map (fun offset => (0,offset))).mapM
    (fun bi => s.memory ⟨.global,0,bi.1,bi.2⟩) : Option (List α))=_
  rewrite [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.rows*50257))
    (fun offset => s.memory (globalCell 0 offset)) (sourceOutputValue ops input)
    (by intro offset ho; exact hv offset (List.mem_range.mp ho))

theorem initial_fixed_grid_flat_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (offset : Nat) (ho : offset<p.rows*50257) :
    (fixedInitialGrid p ops input outside).memory (globalCell 0 offset)=some (sourceOutputValue ops input offset) := by
  have hr : offset/50257<p.rows := by omega
  have hc : offset%50257<50257 := Nat.mod_lt _ (by decide)
  have he : address (offset/50257) (offset%50257)=offset := by unfold address; omega
  have hv := initial_fixed_grid_output p ops input outside (offset/50257) (offset%50257) hr hc
  rewrite [he] at hv
  exact hv

theorem initial_fixed_grid_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout p) (fixedInitialGrid p ops input outside)=some (sourceOrderedSpec p ops input) :=
  source_extract_of_values p ops input _ (initial_fixed_grid_flat_output p ops input outside)

/-- The unchanged partition-aware machine's complete Correct relation for the
bound repaired source, geometry and original fuel, against its explicit formula. -/
theorem source_order_correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program true) (sourceOrderedSpec p ops) := by
  intro input outside
  exact ⟨fixedInitialGrid p ops input outside,initial_fixed_launch p ops input outside,
    initial_fixed_grid_race_free p ops input outside,initial_fixed_grid_extract p ops input outside⟩

#print axioms source_ordered_spec_length
#print axioms source_extract_of_values
#print axioms initial_fixed_grid_flat_output
#print axioms initial_fixed_grid_extract
#print axioms source_order_correct
end LarkNativeSoftmax
