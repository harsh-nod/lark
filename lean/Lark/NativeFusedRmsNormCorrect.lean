import Lark.NativeFusedRmsNormGrid
import Lark.InOutPartition

/-! Whole native seeded-inout source-order correctness. The final extracted list
contains every normalized value followed by every rounded residual value.
Canonical-real/IEEE/reference equivalence remains a separate obligation.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * 16384)).map (fun i => outputResult ops input (i / 16384) (i % 16384)) ++
  (List.range (p.rows * 16384)).map (fun i => residualResult ops input (i / 16384) (i % 16384))

theorem extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hv0 : ∀ i, i < p.rows * 16384 → s.memory (globalCell 0 i) = some (outputResult ops input (i / 16384) (i % 16384)))
    (hv1 : ∀ i, i < p.rows * 16384 → s.memory (globalCell 1 i) = some (residualResult ops input (i / 16384) (i % 16384))) :
    extract (layout p) s = some (spec p ops input) := by
  have h0 := LarkPointwise.mapM_some (List.range (p.rows * 16384))
    (fun i => s.memory (globalCell 0 i)) (fun i => outputResult ops input (i / 16384) (i % 16384))
    (by intro i hi; exact hv0 i (List.mem_range.mp hi))
  have h1 := LarkPointwise.mapM_some (List.range (p.rows * 16384))
    (fun i => s.memory (globalCell 1 i)) (fun i => residualResult ops input (i / 16384) (i % 16384))
    (by intro i hi; exact hv1 i (List.mem_range.mp hi))
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,List.flatMap_nil]
  simp only [List.map_cons,List.map_nil,show Role.input ≠ Role.output by decide,↓reduceIte,
    List.nil_append,List.append_nil]
  change (((List.range (p.rows * 16384)).map (fun i => (0,i)) ++
    (List.range (p.rows * 16384)).map (fun i => (1,i))).mapM
      (fun (bi : Nat × Nat) => s.memory ⟨.global,0,bi.1,bi.2⟩) : Option (List α)) = _
  rewrite [List.mapM_append,LarkPointwise.mapM_map,LarkPointwise.mapM_map]
  simp only [globalCell] at h0 h1
  simp only [h0,h1,bind,pure,Option.some_bind,spec]

theorem final_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout p) (finalState p ops input outside) = some (spec p ops input) := by
  apply extract_of_values p ops input (finalState p ops input outside)
  · intro i hi
    have hr : i / 16384 < p.rows := by omega
    have hc : i % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have he : address (i / 16384) (i % 16384) = i := by unfold address; omega
    have h := (final_values p ops input outside (i / 16384) hr (i % 16384) hc).1
    exact (congrArg (fun l => (finalState p ops input outside).memory l) (congrArg (globalCell 0) he)).symm.trans h
  · intro i hi
    have hr : i / 16384 < p.rows := by omega
    have hc : i % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have he : address (i / 16384) (i % 16384) = i := by unfold address; omega
    have h := (final_values p ops input outside (i / 16384) hr (i % 16384) hc).2
    exact (congrArg (fun l => (finalState p ops input outside).memory l) (congrArg (globalCell 1) he)).symm.trans h

theorem correct (p : Shape) (ops : Ops α) :
    LarkInOutPartition.Correct ops (layout p) mutableBuffers (geometry p) fuel program (spec p ops) := by
  refine ⟨interface_valid p,?_⟩
  intro input outside
  have h := final_exec p ops input outside
  exact ⟨finalState p ops input outside,h.1,h.2,final_extract p ops input outside⟩

#print axioms extract_of_values
#print axioms final_extract
#print axioms correct
end LarkNativeFusedRmsNorm
