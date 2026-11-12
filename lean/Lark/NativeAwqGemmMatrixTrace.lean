import Lark.NativeAwqGemmStagingTrace

/-! Every actual operand shared-read event occurs at the even middle epoch.
Native matrix updates retain the trace, so both complete passes stay good. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoaded operandLoop operandLaneState operandFold blockOperands
  matrixState matrixBankState matrixFold matrixPassState matrixPhaseState

theorem operand_loaded_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e : Nat) (left : Bool) (s : State α) (good : GoodTrace p s)
    (even : (s.epochs t).block%2=0) : GoodTrace p (operandLoaded p ops input tile t half bank left e s) := by
  unfold operandLoaded fragmentLoaded
  apply good_record p s t _ false good
  cases left <;> exact good_operand_event p t _ _ (s.epochs t) even

theorem operand_loop_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e n : Nat) (left : Bool) (s : State α) (good : GoodTrace p s)
    (even : (s.epochs t).block%2=0) : GoodTrace p (operandLoop p ops input tile t half bank left e n s) := by
  induction n generalizing e s with
  | zero => simpa only [operandLoop] using good
  | succ n ih =>
    rw [operandLoop]
    exact ih (e+1) _ (operand_loaded_good p ops input tile t half bank e left s good even)
      (by unfold operandLoaded; exact even)

theorem operand_before_b_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) (good : GoodTrace p s) (even : (s.epochs t).block%2=0) :
    GoodTrace p (operandBeforeB p ops input tile t half bank s) := by
  unfold operandBeforeB
  split
  · exact operand_loop_good p ops input tile t half bank 0 4 true s good even
  · exact good

theorem operand_lane_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (s : State α) (good : GoodTrace p s) (even : (s.epochs t).block%2=0) :
    GoodTrace p (operandLaneState p ops input tile t half bank s) := by
  unfold operandLaneState
  exact operand_loop_good p ops input tile t half bank 0 4 false _ (operand_before_b_good p ops input tile t half bank s good even)
    (by rw [(operand_before_b_frames p ops input tile t half bank s).2.2]; exact even)

theorem operand_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank : Nat) (ts : List Nat) (s : State α) (good : GoodTrace p s)
    (even : ∀ t∈ts, (s.epochs t).block%2=0) : GoodTrace p (operandFold p ops input tile half bank ts s) := by
  induction ts generalizing s with
  | nil => simpa only [operandFold,List.foldl_nil] using good
  | cons t ts ih =>
    have next := operand_lane_good p ops input tile t half bank s good (even t (by simp))
    have rest := ih (operandLaneState p ops input tile t half bank s) next
      (fun u hu => by rw [(operand_lane_frames p ops input tile t half bank s).2.2]; exact even u (List.mem_cons_of_mem t hu))
    simpa only [operandFold,List.foldl_cons] using rest

theorem matrix_bank_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (even : BlockParity p b 0 s) : GoodTrace p (matrixBankState p ops input tile b half bank acc s) := by
  unfold matrixBankState
  apply good_trace_of_trace p (blockOperands p ops input tile b half bank s) _
    (by unfold blockOperands; exact operand_fold_good p ops input tile half bank _ s good even)
  unfold matrixState
  rfl

theorem matrix_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank n : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (even : BlockParity p b 0 s) : GoodTrace p (matrixFold p ops input tile b half acc bank n s) := by
  induction n generalizing bank s with
  | zero => simpa only [matrixFold] using good
  | succ n ih =>
    rw [matrixFold]
    exact ih (bank+1) _ (matrix_bank_good p ops input tile b half bank (acc bank) s good even)
      (by intro t ht; rw [(matrix_bank_frames p ops input tile b half bank (acc bank) s).2.2]; exact even t ht)

theorem matrix_phase_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (acc : Nat → Nat → Nat → α) (s : State α) (good : GoodTrace p s)
    (even : BlockParity p b 0 s) : GoodTrace p (matrixPhaseState p ops input tile b acc s) := by
  unfold matrixPhaseState matrixPassState
  exact matrix_fold_good p ops input tile b 1 0 (banks p) _ _
    (matrix_fold_good p ops input tile b 0 0 (banks p) acc s good even)
    (by intro t ht; rw [(matrix_fold_frames p ops input tile b 0 0 (banks p) acc s).2.2]; exact even t ht)

#print axioms operand_loaded_good
#print axioms operand_loop_good
#print axioms operand_before_b_good
#print axioms operand_lane_good
#print axioms operand_fold_good
#print axioms matrix_bank_good
#print axioms matrix_fold_good
#print axioms matrix_phase_good
end LarkNativeAwqGemm
