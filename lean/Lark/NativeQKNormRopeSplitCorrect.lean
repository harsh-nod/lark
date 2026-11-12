import Lark.NativeQKNormRopeSplitGrid

/-! Whole native split launch correctness against its explicit source-order
expression. Dense canonical-real reference equality remains a separate obligation. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitSourceSpec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * 5120)).map (fun i => splitSourceResult ops input (i / 4) (i % 4))

theorem split_source_spec_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) :
    (splitSourceSpec p ops input).length = p.rows * 5120 := by simp [splitSourceSpec]

theorem split_final_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * 5120) :
    (splitFinalState p ops input outside).memory (globalCell 0 i) =
      some (splitSourceResult ops input (i / 4) (i % 4)) := by
  have ht : i / 4 < p.rows * 1280 := by omega
  have he : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have addr : outputAddress (i / 4) (i % 4) = i := by rw [output_linear]; omega
  have value := split_grid_value p ops input (i / 4) (i % 4) (initial (layout p) input outside) ht he
  simpa only [addr] using value

theorem split_extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv : ∀ i, i < p.rows * 5120 → s.memory (globalCell 0 i) = some (splitSourceResult ops input (i / 4) (i % 4))) :
    extract (layout p) s = some (splitSourceSpec p ops input) := by
  have values := LarkPointwise.mapM_some (List.range (p.rows * 5120))
    (fun i => s.memory (globalCell 0 i)) (fun i => splitSourceResult ops input (i / 4) (i % 4))
    (by intro i hi; exact hv i (List.mem_range.mp hi))
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide, ↓reduceIte,
    List.nil_append, List.append_nil]
  change (((List.range (p.rows * 5120)).map (fun i => (0, i))).mapM
    (fun (bi : Nat × Nat) => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact values

theorem split_final_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p) (splitFinalState p ops input outside) = some (splitSourceSpec p ops input) :=
  split_extract_of_values p ops input _ (split_final_output p ops input outside)

theorem split_source_correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program true) (splitSourceSpec p ops) := by
  intro input outside
  exact ⟨splitFinalState p ops input outside, split_final_launch p ops input outside,
    split_final_race_free p ops input outside, split_final_extract p ops input outside⟩

theorem split_source_correct_from_pre (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (s : State α) (hp : StdPre (layout p) input s) : ∃ final,
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) s = some final ∧
      raceFree (geometry p) final.trace = true ∧ extract (layout p) final = some (splitSourceSpec p ops input) := by
  obtain ⟨outside, rfl⟩ := hp
  exact split_source_correct p ops input outside

theorem split_final_readonly (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Reads p input (splitFinalState p ops input outside) :=
  split_grid_reads p ops input _ (initial_reads p input outside)

theorem split_final_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : (splitFinalState p ops input outside).trace.length = p.rows * 25600 := by
  simpa only [initial, List.length_nil, Nat.zero_add] using
    split_grid_trace_length p ops input (initial (layout p) input outside)

#print axioms split_source_spec_length
#print axioms split_final_output
#print axioms split_extract_of_values
#print axioms split_final_extract
#print axioms split_source_correct
#print axioms split_source_correct_from_pre
#print axioms split_final_readonly
#print axioms split_final_trace_length
end LarkNativeQKNormRope
