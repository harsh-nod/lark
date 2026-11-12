import Lark.NativeQKNormRopeGeometry
import Lark.NativeQKNormRopeInterleavedWave

/-! Global indexing of the source-order interleaved output expression.
Dense-reference equality is a separate obligation. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedSourceResult (ops : Ops α) (input : Nat → Nat → α) (t e : Nat) : α :=
  ops.toHalf (interleavedOutput ops input
    (fun r => normalizedValue ops input t (weightBuffer t)
      (normalScale ops (waveValues ops input (physicalBlock t) (physicalWarp t) 5 (physicalLane t))) r) t e)

theorem interleaved_source_result_cohort (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane e : Nat) (hw : warp < 4) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    interleavedSourceResult ops input t e = ops.toHalf (interleavedOutput ops input
      (fun r => normalizedValue ops input t (weightBuffer t)
        (normalScale ops (waveValues ops input block warp 5 lane)) r) t e) := by
  have coords := physical_coords block warp lane hw hl
  dsimp only [interleavedSourceResult]
  rw [coords.1, coords.2.1, coords.2.2]

theorem interleaved_wave_global_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (block warp t e : Nat) (s : State α) (hw : warp < 4) (ht : t ∈ cohortThreads block warp 64) (he : e < 4) :
    (interleavedWaveState p ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (interleavedSourceResult ops input t e) := by
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
  exact (interleaved_wave_value p ops input block warp lane e s hl he).trans
    (congrArg some (interleaved_source_result_cohort ops input block warp lane e hw hl).symm)

#print axioms interleaved_source_result_cohort
#print axioms interleaved_wave_global_value
end LarkNativeQKNormRope
