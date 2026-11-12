import LarkReal.NativeQKNormRopeDense
import Lark.NativeQKNormRopeSplitResult

/-! Independent dense exact-real split-half normalization/rotary formulas.
The rotary partner is proved to be the other half of the same normalized head. -/
namespace LarkReal.NativeQKNormRope
open LarkNativeQKNormRope
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def denseSplit (input : Nat → Nat → ℝ) (r h c : Nat) : ℝ :=
  let j := c % 64
  let x := denseNormalized input r h j
  let y := denseNormalized input r h (j + 64)
  let cosine := input 4 (r * 128 + j)
  let sine := input 4 (r * 128 + j + 64)
  if c < 64 then x * cosine + (-y) * sine else y * cosine + x * sine

theorem split_normalized_dense (input : Nat → Nat → ℝ) (block warp lane e : Nat) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    splitWaveNormal ops input block warp lane e = denseNormalized input (row t) (head t) (column t e) := by
  dsimp only [splitWaveNormal]
  rw [wave_sum_eq_dense input block warp lane hl]
  simp [normalizedValue, inputValue, weightValue, normalScale, ops, denseNormalized,
    denseScale, inputAddress, weightBuffer]

theorem split_peer_geometry (block warp lane : Nat) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    let peer := cohortBase block warp + xorPeer32 lane 16
    row peer = row t ∧ head peer = head t := by
  have sameHead := xor_peer_same_head block warp lane 16 hl (by decide)
  dsimp only
  unfold row head
  omega

theorem split_partner_column (block warp lane e : Nat) (hl : lane < 64) (he : e < 4) :
    column (cohortBase block warp + xorPeer32 lane 16) e =
      (column (cohortBase block warp + lane) e + 64) % 128 := by
  have table : ∀ l : Fin 64, ∀ c : Fin 4,
      (xorPeer32 l.val 16 % 32) * 4 + c.val = (l.val % 32 * 4 + c.val + 64) % 128 := by decide
  have own : (cohortBase block warp + lane) % 32 = lane % 32 := by unfold cohortBase; omega
  have peer : (cohortBase block warp + xorPeer32 lane 16) % 32 = xorPeer32 lane 16 % 32 := by
    unfold cohortBase; omega
  simpa only [column, own, peer] using table ⟨lane, hl⟩ ⟨e, he⟩

theorem split_cohort_result_dense (input : Nat → Nat → ℝ) (block warp lane e : Nat)
    (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    ops.toHalf (splitWaveResult ops input block warp t e) = denseSplit input (row t) (head t) (column t e) := by
  simp only [splitWaveResult, splitLaneResult, splitRotaryValue, splitWaveValues, splitWavePeers,
    splitLanePartners, Nat.add_sub_cancel_left]
  change splitComponent ops (splitWaveNormal ops input block warp lane e)
    (splitSignedPartner ops (cohortBase block warp + lane)
      (splitWaveNormal ops input block warp (xorPeer32 lane 16) e))
    (splitCosValue ops input (cohortBase block warp + lane) e)
    (splitSinValue ops input (cohortBase block warp + lane) e) = _
  rw [split_normalized_dense input block warp lane e hl,
    split_normalized_dense input block warp (xorPeer32 lane 16) e
      (xor_peer_bound 64 lane 16 (Or.inr rfl) hl (by decide))]
  have coords := split_peer_geometry block warp lane hl
  rw [coords.1, coords.2, split_partner_column block warp lane e hl he]
  have colBound : column (cohortBase block warp + lane) e < 128 := by
    unfold column
    have h := Nat.mod_lt (cohortBase block warp + lane) (by decide : 0 < 32)
    omega
  by_cases lower : (cohortBase block warp + lane) % 32 < 16
  · have colLower : column (cohortBase block warp + lane) e < 64 := by unfold column; omega
    have partner : (column (cohortBase block warp + lane) e + 64) % 128 =
        column (cohortBase block warp + lane) e + 64 := Nat.mod_eq_of_lt (by omega)
    simp [splitComponent, splitSignedPartner, splitCosValue, splitSinValue, splitCosAddress,
      splitSinAddress, denseSplit, ops, lower, colLower, partner, Nat.mod_eq_of_lt colLower]
  · have colUpper : ¬ column (cohortBase block warp + lane) e < 64 := by unfold column; omega
    have partner : (column (cohortBase block warp + lane) e + 64) % 128 =
        column (cohortBase block warp + lane) e % 64 := by omega
    have own : column (cohortBase block warp + lane) e % 64 + 64 =
        column (cohortBase block warp + lane) e := by omega
    simp [splitComponent, splitSignedPartner, splitCosValue, splitSinValue, splitCosAddress,
      splitSinAddress, denseSplit, ops, lower, colUpper, partner, own]

theorem split_result_eq_dense (input : Nat → Nat → ℝ) (t e : Nat) (he : e < 4) :
    splitSourceResult ops input t e = denseSplit input (row t) (head t) (column t e) := by
  simpa only [physical_reconstruct] using
    split_cohort_result_dense input (physicalBlock t) (physicalWarp t) (physicalLane t) e (physical_lane_bound t) he

#print axioms split_normalized_dense
#print axioms split_peer_geometry
#print axioms split_partner_column
#print axioms split_cohort_result_dense
#print axioms split_result_eq_dense
end LarkReal.NativeQKNormRope
