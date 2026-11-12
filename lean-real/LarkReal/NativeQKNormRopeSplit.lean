import LarkReal.NativeQKNormRopeSplitDense
import Lark.NativeQKNormRopeSplitCorrect

/-! Complete native split-half launch equals an independent dense exact-real
RMS normalization and rotary reference. Storage conversions are identities in
this interpretation, as in the pinned exact-real operation model. -/
namespace LarkReal.NativeQKNormRope.Split
open LarkNonlinear LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def denseSpec (p : Shape) (input : Nat → Nat → ℝ) : List ℝ :=
  (List.range (p.rows * 5120)).map (fun i => denseSplit input (i / 5120) (i % 5120 / 128) (i % 128))

theorem dense_spec_length (p : Shape) (input : Nat → Nat → ℝ) :
    (denseSpec p input).length = p.rows * 5120 := by simp [denseSpec]

theorem spec_eq_dense (p : Shape) (input : Nat → Nat → ℝ) :
    splitSourceSpec p ops input = denseSpec p input := by
  unfold splitSourceSpec denseSpec
  apply List.map_congr_left
  intro i _
  have coords := flat_coords i
  simpa only [coords.1, coords.2.1, coords.2.2] using split_result_eq_dense input (i / 4) (i % 4) (Nat.mod_lt _ (by decide))

theorem final_output (p : Shape) (input : Nat → Nat → ℝ) (outside : Location → Option ℝ)
    (i : Nat) (hi : i < p.rows * 5120) :
    (splitFinalState p ops input outside).memory (globalCell 0 i) =
      some (denseSplit input (i / 5120) (i % 5120 / 128) (i % 128)) := by
  have coords := flat_coords i
  have value := split_result_eq_dense input (i / 4) (i % 4) (Nat.mod_lt _ (by decide))
  exact (split_final_output p ops input outside i hi).trans
    (congrArg some (by simpa only [coords.1, coords.2.1, coords.2.2] using value))

theorem final_extract (p : Shape) (input : Nat → Nat → ℝ) (outside : Location → Option ℝ) :
    extract (layout p) (splitFinalState p ops input outside) = some (denseSpec p input) :=
  (split_final_extract p ops input outside).trans (congrArg some (spec_eq_dense p input))

theorem correct (p : Shape) :
    LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program true) (denseSpec p) := by
  intro input outside
  exact ⟨splitFinalState p ops input outside, split_final_launch p ops input outside,
    split_final_race_free p ops input outside, final_extract p input outside⟩

theorem correct_from_pre (p : Shape) (input : Nat → Nat → ℝ) (s : State ℝ)
    (hp : StdPre (layout p) input s) : ∃ final,
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) s = some final ∧
      raceFree (geometry p) final.trace = true ∧ extract (layout p) final = some (denseSpec p input) := by
  obtain ⟨outside, rfl⟩ := hp
  exact correct p input outside

#print axioms dense_spec_length
#print axioms spec_eq_dense
#print axioms final_output
#print axioms final_extract
#print axioms correct
#print axioms correct_from_pre
end LarkReal.NativeQKNormRope.Split
