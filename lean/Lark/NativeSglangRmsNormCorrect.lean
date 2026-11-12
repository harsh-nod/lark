import Lark.NativeSglangRmsNormGrid
import Lark.Pointwise

/-! Complete guarded native source-ordered correctness for every supported
shape and every scalar interpretation. Dense real RMSNorm equality is separate
from this arbitrary-Ops theorem; lane-specific inverse values remain explicit.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def spec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows*16384)).map (fun offset => sourceResult ops input (offset/16384) (offset%16384))

theorem extract_of_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (values : ∀ offset,offset<p.rows*16384 → s.memory (globalCell 0 offset)=
      some (sourceResult ops input (offset/16384) (offset%16384))) :
    extract (layout p) s=some (spec p ops input) := by
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,List.flatMap_nil]
  simp only [List.map_cons,List.map_nil,show Role.input≠Role.output by decide,
    ↓reduceIte,List.nil_append,List.append_nil]
  change (((List.range (p.rows*16384)).map (fun i => (0,i))).mapM
    (fun bi => s.memory ⟨.global,0,bi.1,bi.2⟩) : Option (List α))=_
  rw [LarkPointwise.mapM_map]
  exact LarkPointwise.mapM_some (List.range (p.rows*16384))
    (fun i => s.memory (globalCell 0 i)) (fun i => sourceResult ops input (i/16384) (i%16384))
    (by intro i hi; exact values i (List.mem_range.mp hi))

theorem final_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (layout p) (finalState p ops input outside)=some (spec p ops input) :=
  extract_of_values p ops input (finalState p ops input outside) (final_global_value p ops input outside)

theorem correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program true) (spec p ops) := by
  intro input outside
  have h := final_exec p ops input outside
  exact ⟨finalState p ops input outside,h.1,h.2,final_extract p ops input outside⟩

#print axioms extract_of_values
#print axioms final_extract
#print axioms correct
end LarkNativeSglangRmsNorm
