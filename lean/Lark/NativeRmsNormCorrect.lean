import Lark.NativeRmsNormGrid

/-! Whole actual native RMSNorm correctness: source execution, actual-trace race
freedom and extraction of every specified output, for all inputs/outside memory.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv : ∀ i, i < p.rows * 16384 → s.memory (globalCell 0 i) =
      some (result ops input (i / 16384) (i % 16384))) :
    extract (layout p) s = some (spec p ops input) := by
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide,
    ↓reduceIte, List.nil_append, List.append_nil]
  change (((List.range (p.rows * 16384)).map (fun i => (0, i))).mapM
    (fun bi => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rewrite [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.rows * 16384))
    (fun i => s.memory (globalCell 0 i)) (fun i => result ops input (i / 16384) (i % 16384))
    (by intro i hi; exact hv i (List.mem_range.mp hi))

theorem final_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout p) (finalState p ops input outside) = some (spec p ops input) := by
  apply extract_of_values p ops input (finalState p ops input outside)
  intro i hi
  have hr : i / 16384 < p.rows := by omega
  have hc : i % 16384 < 16384 := Nat.mod_lt _ (by decide)
  have he : i / 16384 * 16384 + i % 16384 = i := by have h := Nat.div_add_mod i 16384; omega
  have h := final_value p ops input outside (i / 16384) (i % 16384) hr hc
  exact (congrArg (fun l => (finalState p ops input outside).memory l) (congrArg (globalCell 0) he)).symm.trans h

/-- The machine's original whole-launch `Correct` relation, with the fixed native
geometry, program, fuel and independently declared source-tree specification. -/
theorem correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel program (spec p ops) := by
  intro input outside
  have h := final_exec p ops input outside
  exact ⟨finalState p ops input outside, h.1, h.2, final_extract p ops input outside⟩

#print axioms correct
end LarkNativeRmsNorm
