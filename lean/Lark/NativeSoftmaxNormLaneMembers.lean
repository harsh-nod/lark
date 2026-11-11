import Lark.NativeSoftmaxNormRoundMembers

/-! A selected component access occurs in the complete actual normalization
lane. Count-parametric transport avoids evaluating an entire concrete lane
inside the proof kernel; seven rounds are the final source specialization. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_lane_sequence_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row tid count iteration component : Nat) (s : State α) (hi : iteration<count) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈
      (normExit false (row*1024+tid)
        (normRounds false ops input row tid 0 count (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s))).trace := by
  have hm := norm_rounds_event_member false ops input row tid 0 count iteration
    (normReadAccess row tid iteration component)
    (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s) (by omega) (by omega)
    (fun state => norm_round_original_member ops input row tid iteration component state hc)
  simpa only [normExit,advance,(norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).2.1] using hm

theorem norm_lane_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hi : iteration<7) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈ (normLaneState false ops input row tid s).trace :=
  norm_lane_sequence_original_member ops input row tid 7 iteration component s hi hc

theorem norm_lane_sequence_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid count iteration component : Nat) (s : State α)
    (hi : iteration<count) (hc : component<8) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈
      (normExit guarded (row*1024+tid)
        (normRounds guarded ops input row tid 0 count (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s))).trace := by
  have hm := norm_rounds_event_member guarded ops input row tid 0 count iteration
    (normWriteAccess row tid iteration component)
    (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s) (by omega) (by omega)
    (fun state => norm_round_valid_member guarded ops input row tid iteration component state hc hcol)
  simpa only [normExit,advance,(norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).2.1] using hm

theorem norm_lane_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈ (normLaneState guarded ops input row tid s).trace :=
  norm_lane_sequence_valid_member guarded ops input row tid 7 iteration component s hi hc hcol

#print axioms norm_lane_sequence_original_member
#print axioms norm_lane_original_member
#print axioms norm_lane_sequence_valid_member
#print axioms norm_lane_valid_member
end LarkNativeSoftmax
