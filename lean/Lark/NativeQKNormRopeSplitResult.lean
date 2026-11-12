import Lark.NativeQKNormRopeGeometry
import Lark.NativeQKNormRopeSplitWave

/-! Global indexing of the explicit split-half source-order output expression.
Dense exact-real reference equality is a separate obligation. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitSourceResult (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.toHalf (splitWaveResult ops input (physicalBlock t) (physicalWarp t) t e)

theorem split_source_result_cohort (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane e : Nat) (hw : warp < 4) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    splitSourceResult ops input t e = ops.toHalf (splitWaveResult ops input block warp t e) := by
  have coords := physical_coords block warp lane hw hl
  dsimp only [splitSourceResult]
  rw [coords.1, coords.2.1]

theorem split_wave_global_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp t e : Nat) (s : State α) (hw : warp < 4) (ht : t ∈ cohortThreads block warp 64) (he : e < 4) :
    (splitWaveState p ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (splitSourceResult ops input t e) := by
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
  exact (split_wave_value p ops input block warp lane e s hl he).trans
    (congrArg some (split_source_result_cohort ops input block warp lane e hw hl).symm)

#print axioms split_source_result_cohort
#print axioms split_wave_global_value
end LarkNativeQKNormRope
