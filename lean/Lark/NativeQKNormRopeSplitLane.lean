import Lark.NativeQKNormRopeSplitRotary

/-! Actual per-lane split-half continuation from all four snapshots to the
second fence. The raw partners pass the source sign branch before products. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitLanePartners (ops : Ops α) (t : Nat) (peers : Nat → α) (e : Nat) : α :=
  splitSignedPartner ops t (peers e)
def splitLaneResult (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α) (t e : Nat) : α :=
  splitRotaryValue ops input values (splitLanePartners ops t peers) t e

def splitRotaryLane (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) : State α :=
  splitRotaryFour ops input values (splitLanePartners ops t peers) t (splitSigned ops t peers s)

theorem split_rotary_lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 64)
    (hv : SplitRotaryInputs values peers t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra + (splitSignSteps t + 28)) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
        (splitRotaryLane ops input values peers t s) := by
  rw [show extra + (splitSignSteps t + 28) = (extra + 28) + splitSignSteps t by omega,
    split_signed_eq p ops t (extra + 28) peers s hp hi.2.2.1 hv.2]
  apply split_rotary_parts_run p ops input values (splitLanePartners ops t peers) t 0 4 extra _ ht (by decide)
    (split_signed_pc ops t peers s)
  · constructor
    · intro e he
      exact (split_signed_low ops t (18 + 2 * e) peers s (by omega)).trans (hv.1 e he)
    · intro e he; exact split_signed_value ops t e peers s he hv.2
  · simpa only [NativeIndices, (split_signed_preserves ops t peers s).2.1] using hi
  · simpa only [Reads, (split_signed_preserves ops t peers s).1] using hr

theorem split_rotary_lane_pc (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) : (splitRotaryLane ops input values peers t s).pc t = 97 :=
  split_rotary_four_pc ops input values (splitLanePartners ops t peers) t _

theorem split_rotary_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 64)
    (hv : SplitRotaryInputs values peers t s) (hi : NativeIndices t s) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s =
      some (splitRotaryLane ops input values peers t s) := by
  have steps : splitSignSteps t ≤ 5 := by unfold splitSignSteps; split <;> omega
  have count : fuel.lane = (227 - splitSignSteps t + 1) + (splitSignSteps t + 28) := by
    change 256 = _; omega
  rw [count, split_rotary_lane_eq p ops input values peers t (227 - splitSignSteps t + 1) s ht hp hv hi hr]
  have parked : LarkCollective.parked (program true) (splitRotaryLane ops input values peers t s) t = some .warp := by
    simp only [LarkCollective.parked, split_rotary_lane_pc, split_barrier_code 97 (Or.inr rfl)]
    rfl
  simp only [LarkCollective.runLane, parked]

theorem split_rotary_lane_value (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t e : Nat) (s : State α) (he : e < 4) :
    (splitRotaryLane ops input values peers t s).regs t (33 + 5 * e) =
      some (splitLaneResult ops input values peers t e) :=
  split_rotary_parts_value ops input values (splitLanePartners ops t peers) t 0 4 e _ ⟨by omega, he⟩

theorem split_rotary_lane_index (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t r : Nat) (s : State α) (hr : r < 15) :
    (splitRotaryLane ops input values peers t s).indices t r = s.indices t r :=
  (split_rotary_parts_index ops input values (splitLanePartners ops t peers) t 0 4 r _ hr).trans
    (congrFun (congrFun (split_signed_preserves ops t peers s).2.1 t) r)

theorem split_rotary_lane_preserves (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) :
    (splitRotaryLane ops input values peers t s).memory = s.memory ∧
    (splitRotaryLane ops input values peers t s).epochs = s.epochs := by
  have parts := split_rotary_parts_preserves ops input values (splitLanePartners ops t peers) t 0 4 (splitSigned ops t peers s)
  have sign := split_signed_preserves ops t peers s
  exact ⟨parts.1.trans sign.1, parts.2.trans sign.2.2.1⟩

theorem split_rotary_lane_trace_length (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) :
    (splitRotaryLane ops input values peers t s).trace.length = s.trace.length + 8 := by
  have count := split_rotary_parts_trace_length ops input values (splitLanePartners ops t peers) t 0 4
    (splitSigned ops t peers s)
  simpa only [(split_signed_preserves ops t peers s).2.2.2] using count

theorem split_rotary_lane_good (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t : Nat) (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (splitRotaryLane ops input values peers t s).trace, Good a := by
  apply split_rotary_parts_good
  simpa only [(split_signed_preserves ops t peers s).2.2.2] using good

theorem split_rotary_lane_other (ops : Ops α) (input : Nat → Nat → α) (values peers : Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) :
    (splitRotaryLane ops input values peers t s).pc u = s.pc u ∧
    (splitRotaryLane ops input values peers t s).indices u = s.indices u ∧
    (splitRotaryLane ops input values peers t s).regs u = s.regs u := by
  have later := split_rotary_parts_other ops input values (splitLanePartners ops t peers) t 0 4 u
    (splitSigned ops t peers s) hu
  have first := split_signed_other ops t u peers s hu
  exact ⟨later.1.trans first.1, later.2.1.trans (congrFun (split_signed_preserves ops t peers s).2.1 u),
    later.2.2.trans first.2⟩

#print axioms split_rotary_lane_eq
#print axioms split_rotary_lane_pc
#print axioms split_rotary_lane_run
#print axioms split_rotary_lane_value
#print axioms split_rotary_lane_index
#print axioms split_rotary_lane_preserves
#print axioms split_rotary_lane_trace_length
#print axioms split_rotary_lane_good
#print axioms split_rotary_lane_other
end LarkNativeQKNormRope
