import Lark.NativeRopeGrid
import Lark.NativeRopeDense
import Lark.InOutScalar

/-! Complete native initialized-inout correctness and source-ordered extraction
of both Q/K buffers against an independent dense column-indexed reference. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def spec (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.rows * 4096)).map (fun i => denseResult ops input 0 (i / 4096) (i % 4096) neox) ++
  (List.range (p.rows * 1024)).map (fun i => denseResult ops input 1 (i / 1024) (i % 1024) neox)

theorem spec_length (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) :
    (spec p neox ops input).length = p.rows * 5120 := by
  simp only [spec, List.length_append, List.length_map, List.length_range]
  omega

theorem final_query_output (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * 4096) :
    (finalState p neox ops input outside).memory (globalCell 0 i) =
      some (denseResult ops input 0 (i / 4096) (i % 4096) neox) := by
  have hr : i / 4096 < p.rows := by omega
  have hc : i % 4096 < 4096 := Nat.mod_lt _ (by decide)
  obtain ⟨pair, hp, imaginary, hcol⟩ := column_coverage neox 32 (i % 4096) hc
  let t := i / 4096 * 512 + pair % 512
  have ht : t < p.rows * 512 := by dsimp [t]; have hm := Nat.mod_lt pair (by decide : 0 < 512); omega
  have co := thread_coordinates (i / 4096) (pair % 512) t (Nat.mod_lt _ (by decide)) rfl
  have hv := (final_completed p neox ops input outside t ht).1 (pair / 512) (by omega) imaginary
  have he : pair % 512 + pair / 512 * 512 = pair := by omega
  have hm : (finalState p neox ops input outside).memory (globalCell 0 (address 0 (i / 4096) pair neox imaginary)) =
      some (rotated ops input 0 (i / 4096) pair neox imaginary) := by
    simpa only [co.1, co.2, he] using hv
  have ha : address 0 (i / 4096) pair neox imaginary = i := by
    simp only [address, width, ↓reduceIte]
    rw [hcol]
    omega
  rw [ha] at hm
  have hd := dense_at_pair ops input 0 (i / 4096) pair neox imaginary
  rw [hcol] at hd
  rw [← hd] at hm
  exact hm

theorem final_key_output (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < p.rows * 1024) :
    (finalState p neox ops input outside).memory (globalCell 1 i) =
      some (denseResult ops input 1 (i / 1024) (i % 1024) neox) := by
  have hr : i / 1024 < p.rows := by omega
  have hc : i % 1024 < 1024 := Nat.mod_lt _ (by decide)
  obtain ⟨pair, hp, imaginary, hcol⟩ := column_coverage neox 8 (i % 1024) hc
  let t := i / 1024 * 512 + pair
  have ht : t < p.rows * 512 := by dsimp [t]; omega
  have co := thread_coordinates (i / 1024) pair t hp rfl
  have hv := (final_completed p neox ops input outside t ht).2 imaginary
  have hm : (finalState p neox ops input outside).memory (globalCell 1 (address 1 (i / 1024) pair neox imaginary)) =
      some (rotated ops input 1 (i / 1024) pair neox imaginary) := by
    simpa only [co.1, co.2] using hv
  have ha : address 1 (i / 1024) pair neox imaginary = i := by
    simp only [address, width, show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
    rw [hcol]
    omega
  rw [ha] at hm
  have hd := dense_at_pair ops input 1 (i / 1024) pair neox imaginary
  rw [hcol] at hd
  rw [← hd] at hm
  exact hm

theorem extract_of_values (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hq : ∀ i, i < p.rows * 4096 → s.memory (globalCell 0 i) = some (denseResult ops input 0 (i / 4096) (i % 4096) neox))
    (hk : ∀ i, i < p.rows * 1024 → s.memory (globalCell 1 i) = some (denseResult ops input 1 (i / 1024) (i % 1024) neox)) :
    extract (layout p) s = some (spec p neox ops input) := by
  have h0 := LarkPointwise.mapM_some (List.range (p.rows * 4096))
    (fun i => s.memory (globalCell 0 i)) (fun i => denseResult ops input 0 (i / 4096) (i % 4096) neox)
    (by intro i hi; exact hq i (List.mem_range.mp hi))
  have h1 := LarkPointwise.mapM_some (List.range (p.rows * 1024))
    (fun i => s.memory (globalCell 1 i)) (fun i => denseResult ops input 1 (i / 1024) (i % 1024) neox)
    (by intro i hi; exact hk i (List.mem_range.mp hi))
  simp only [extract, layout, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil]
  simp only [List.map_cons, List.map_nil, show Role.input ≠ Role.output by decide, ↓reduceIte,
    List.nil_append, List.append_nil]
  change (((List.range (p.rows * 4096)).map (fun i => (0, i)) ++
    (List.range (p.rows * 1024)).map (fun i => (1, i))).mapM
      (fun (bi : Nat × Nat) => s.memory ⟨.global, 0, bi.1, bi.2⟩) : Option (List α)) = _
  rewrite [List.mapM_append, LarkPointwise.mapM_map, LarkPointwise.mapM_map]
  simp only [globalCell] at h0 h1
  simp only [h0, h1, bind, pure, Option.some_bind, spec]

theorem final_extract (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    extract (layout p) (finalState p neox ops input outside) = some (spec p neox ops input) :=
  extract_of_values p neox ops input _ (final_query_output p neox ops input outside) (final_key_output p neox ops input outside)

theorem correct (p : Shape) (neox : Bool) (ops : Ops α) :
    LarkInOutScalar.Correct ops (layout p) mutableBuffers (geometry p) fuel (program neox) (spec p neox ops) := by
  refine ⟨interface_valid p, ?_⟩
  intro input outside
  exact ⟨finalState p neox ops input outside, (final_launch p neox ops input outside).1,
    final_race_free p neox ops input outside, final_extract p neox ops input outside⟩

#print axioms spec_length
#print axioms final_query_output
#print axioms final_key_output
#print axioms extract_of_values
#print axioms final_extract
#print axioms correct
end LarkNativeRope
