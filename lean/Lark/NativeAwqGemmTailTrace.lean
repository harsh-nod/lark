import Lark.NativeAwqGemmMatrixTrace

/-! Every actual final-store trace event has the source's unique global
output writer. Counter control and skipped row tails add no memory event. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputStored outputRound outputLoop outputLane tailLane tailFold

theorem output_round_good (p : Shape) (ops : Ops α) (t q : Nat) (values : Nat → α) (s : State α)
    (hq : q<4*banks p) (good : GoodTrace p s) : GoodTrace p (outputRound p ops t q values s) := by
  intro a ha
  rw [output_round_trace] at ha
  split at ha
  · rcases List.mem_cons.mp ha with same | member
    · subst a; exact good_output_event p t q (s.epochs t) hq
    · exact good a member
  · exact good a ha

theorem output_loop_good (p : Shape) (ops : Ops α) (t q n : Nat) (values : Nat → α) (s : State α)
    (hn : q+n≤4*banks p) (good : GoodTrace p s) : GoodTrace p (outputLoop p ops t values q n s) := by
  induction n generalizing q s with
  | zero => simpa only [outputLoop] using good
  | succ n ih =>
    rw [outputLoop]
    exact ih (q+1) _ (by omega) (output_round_good p ops t q values s (by omega) good)

theorem tail_lane_good (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α)
    (good : GoodTrace p s) : GoodTrace p (tailLane p ops tile t values s) := by
  unfold tailLane
  split
  · exact good_trace_of_trace p s _ good rfl
  · unfold outputLane
    exact output_loop_good p ops t 0 (4*banks p) values _ (by omega) (good_trace_of_trace p s _ good rfl)

theorem tail_fold_good (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (good : GoodTrace p s) : GoodTrace p (tailFold p ops tile values ts s) := by
  induction ts generalizing s with
  | nil => simpa only [tailFold,List.foldl_nil] using good
  | cons t ts ih =>
    simpa only [tailFold,List.foldl_cons] using ih (tailLane p ops tile t (values t) s) (tail_lane_good p ops tile t (values t) s good)

theorem block_tail_good (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α)
    (s : State α) (good : GoodTrace p s) : GoodTrace p (blockTail p ops tile b values s) :=
  tail_fold_good p ops tile values _ s good

#print axioms output_round_good
#print axioms output_loop_good
#print axioms tail_lane_good
#print axioms tail_fold_good
#print axioms block_tail_good
end LarkNativeAwqGemm
