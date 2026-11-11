import Lark.NativeSoftmaxMaxRound

/-! Induction over all seven actual outer iterations of the first source pass. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def maxRoundsFold (ops : Ops α) (input : Nat → Nat → α) (row tid : Nat) :
    Nat → Nat → α → α
  | _,0,acc => acc
  | iteration,count+1,acc => maxRoundsFold ops input row tid (iteration+1) count
      (maxFold ops input row tid iteration 0 8 acc)

def maxRounds (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => s
  | iteration,count+1,acc,s => maxRounds ops input row tid t (iteration+1) count
      (maxFold ops input row tid iteration 0 8 acc)
      (maxRoundAfter ops input row tid iteration t acc s)

def maxRoundsCost (tid : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | iteration,count+1 => maxRoundCost tid iteration + maxRoundsCost tid (iteration+1) count

theorem max_rounds_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count : Nat) (acc : α) (s : State α)
    (ready : MaxRoundReady p input row tid iteration t acc s) :
    MaxRoundReady p input row tid (iteration+count) t
      (maxRoundsFold ops input row tid iteration count acc)
      (maxRounds ops input row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => simpa [maxRoundsFold,maxRounds] using ready
  | succ count ih =>
    have head := max_round_ready p ops input row tid iteration t acc s ready
    have tail := ih (iteration+1) _ _ head
    simpa only [maxRoundsFold,maxRounds,
      show iteration+1+count=iteration+(count+1) by omega] using tail

theorem max_rounds_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration+count ≤ 7)
    (ready : MaxRoundReady p input row tid iteration t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra + maxRoundsCost tid iteration count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxRounds ops input row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    have head := max_round_ready p ops input row tid iteration t acc s ready
    simp only [maxRoundsCost,maxRounds]
    rewrite [show extra + (maxRoundCost tid iteration + maxRoundsCost tid (iteration+1) count) =
      (extra + maxRoundsCost tid (iteration+1) count) + maxRoundCost tid iteration by omega]
    rewrite [max_round_eq p guarded ops input row tid iteration t _ acc s hr ht (by omega) ready]
    exact ih (iteration+1) _ _ (by omega) head

theorem max_rounds_cost_bound (tid iteration count : Nat) :
    maxRoundsCost tid iteration count ≤ 77 * count := by
  induction count generalizing iteration with
  | zero => simp [maxRoundsCost]
  | succ count ih =>
    have head := max_round_cost_bound tid iteration
    have tail := ih (iteration+1)
    simp only [maxRoundsCost]
    omega

theorem max_rounds_frames (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count : Nat) (acc : α) (s : State α) :
    (maxRounds ops input row tid t iteration count acc s).memory = s.memory ∧
    (maxRounds ops input row tid t iteration count acc s).epochs = s.epochs ∧
    (maxRounds ops input row tid t iteration count acc s).trace.length = s.trace.length + 8*count := by
  induction count generalizing iteration acc s with
  | zero => exact ⟨rfl,rfl,by simp [maxRounds]⟩
  | succ count ih =>
    obtain ⟨hm,he,ht⟩ := max_round_frames ops input row tid iteration t acc s
    obtain ⟨tailm,taile,tailt⟩ := ih (iteration+1)
      (maxFold ops input row tid iteration 0 8 acc) (maxRoundAfter ops input row tid iteration t acc s)
    refine ⟨tailm.trans hm,taile.trans he,?_⟩
    change (maxRounds ops input row tid t (iteration+1) count _ _).trace.length = _
    rewrite [tailt,ht]
    omega

theorem max_rounds_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid t iteration count r : Nat) (acc : α) (s : State α)
    (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    (maxRounds ops input row tid t iteration count acc s).indices t r = s.indices t r := by
  induction count generalizing iteration acc s with
  | zero => rfl
  | succ count ih =>
    simp only [maxRounds]
    rewrite [ih]
    exact max_round_index_other ops input row tid iteration t r acc s h4 h5 h6 h7

#print axioms max_rounds_ready
#print axioms max_rounds_eq
#print axioms max_rounds_cost_bound
#print axioms max_rounds_frames
#print axioms max_rounds_index_other
end LarkNativeSoftmax
