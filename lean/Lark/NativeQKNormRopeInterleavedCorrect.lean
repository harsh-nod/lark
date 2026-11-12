import Lark.NativeQKNormRopeInterleavedGrid

/-! Whole native interleaved launch correctness against its explicit source-order
expression. Dense canonical-real reference equality remains a separate obligation. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedSourceSpec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * 5120)).map (fun i => interleavedSourceResult ops input (i / 4) (i % 4))

theorem interleaved_source_spec_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) :
    (interleavedSourceSpec p ops input).length = p.rows * 5120 := by simp [interleavedSourceSpec]

theorem interleaved_final_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * 5120) :
    (interleavedFinalState p ops input outside).memory (globalCell 0 i) =
      some (interleavedSourceResult ops input (i / 4) (i % 4)) := by
  have ht : i / 4 < p.rows * 1280 := by omega
  have he : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have addr : outputAddress (i / 4) (i % 4) = i := by rw [output_linear]; omega
  have value := interleaved_grid_value p ops input (i / 4) (i % 4) (initial (layout p) input outside) ht he
  simpa only [addr] using value

theorem interleaved_extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv : ∀ i, i < p.rows * 5120 → s.memory (globalCell 0 i) = some (interleavedSourceResult ops input (i / 4) (i % 4))) :
    extract (layout p) s = some (interleavedSourceSpec p ops input) := by
  have values := LarkPointwise.mapM_some (List.range (p.rows * 5120))
    (fun i => s.memory (globalCell 0 i)) (fun i => interleavedSourceResult ops input (i / 4) (i % 4))
    (by intro i hi; exact hv i (List.mem_range.mp hi))
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide, ↓reduceIte,
    List.nil_append, List.append_nil]
  change (((List.range (p.rows * 5120)).map (fun i => (0, i))).mapM
    (fun (bi : Nat × Nat) => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rw [LarkPointwise.mapM_map]
  exact values

theorem interleaved_final_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p) (interleavedFinalState p ops input outside) = some (interleavedSourceSpec p ops input) :=
  interleaved_extract_of_values p ops input _ (interleaved_final_output p ops input outside)

theorem interleaved_source_correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program false) (interleavedSourceSpec p ops) := by
  intro input outside
  exact ⟨interleavedFinalState p ops input outside, interleaved_final_launch p ops input outside,
    interleaved_final_race_free p ops input outside, interleaved_final_extract p ops input outside⟩

theorem interleaved_source_correct_from_pre (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (s : State α) (hp : StdPre (layout p) input s) : ∃ final,
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program false) s = some final ∧
      raceFree (geometry p) final.trace = true ∧ extract (layout p) final = some (interleavedSourceSpec p ops input) := by
  obtain ⟨outside, rfl⟩ := hp
  exact interleaved_source_correct p ops input outside

theorem interleaved_final_readonly (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Reads p input (interleavedFinalState p ops input outside) :=
  interleaved_grid_reads p ops input _ (initial_reads p input outside)

theorem interleaved_final_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : (interleavedFinalState p ops input outside).trace.length = p.rows * 20480 := by
  simpa only [initial, List.length_nil, Nat.zero_add] using
    interleaved_grid_trace_length p ops input (initial (layout p) input outside)

#print axioms interleaved_source_spec_length
#print axioms interleaved_final_output
#print axioms interleaved_extract_of_values
#print axioms interleaved_final_extract
#print axioms interleaved_source_correct
#print axioms interleaved_source_correct_from_pre
#print axioms interleaved_final_readonly
#print axioms interleaved_final_trace_length
end LarkNativeQKNormRope
