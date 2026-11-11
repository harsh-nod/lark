import Lark.NativeSoftmaxNormStart

/-! Instruction identities for both normalization tails. The repair removes
one clamp instruction, shifting the later PCs by one. These facts expose the
real branch targets, private bank1, casts and division operand order. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normPc (guarded : Bool) (fixedPc : Nat) : Nat := fixedPc+if guarded then 0 else 1

theorem norm_pc_next (guarded : Bool) (pc : Nat) : normPc guarded (pc+1)=normPc guarded pc+1 := by
  cases guarded <;> simp [normPc] <;> omega

theorem norm_outer_codes (guarded : Bool) :
    (program guarded)[95]?=some (.scalar (.branch (.lt (.ivar 17) (.const 50257)) (normPc guarded 115))) ∧
    (program guarded)[96]?=some (.scalar (.index 18 (.const 0))) ∧
    (program guarded)[97]?=some (.scalar (.branch (.lt (.ivar 18) (.const 8)) (normPc guarded 104))) := by
  cases guarded <;> decide

theorem norm_load_head_codes (guarded : Bool) :
    (program guarded)[98]?=some (.scalar (.index 19 (.add (.ivar 17) (.mul (.ivar 18) (.const 1024))))) ∧
    (program guarded)[99]?=some (.scalar (if guarded then
      .branch (.lt (.ivar 19) (.const 50257)) 102 else .branch (.le (.const 50257) (.ivar 19)) 101)) := by
  cases guarded <;> decide

theorem norm_original_clamp_code : (program false)[100]?=some (.scalar (.index 19 (.const 50256))) := by decide

theorem norm_load_body_codes (guarded : Bool) :
    (program guarded)[normPc guarded 100]?=some (.scalar (.index 20 (.add (.mul (.ivar 0) (.const 50257)) (.ivar 19)))) ∧
    (program guarded)[normPc guarded 101]?=some (.scalar (.store .local 1 (.ivar 18) (.un .fromHalf (.load .global 0 (.ivar 20))))) ∧
    (program guarded)[normPc guarded 102]?=some (.scalar (.index 18 (.add (.ivar 18) (.const 1)))) ∧
    (program guarded)[normPc guarded 103]?=some (.scalar (.jump 97)) := by
  cases guarded <;> decide

theorem norm_store_init_code (guarded : Bool) :
    (program guarded)[normPc guarded 104]?=some (.scalar (.index 21 (.const 0))) := by
  cases guarded <;> decide

theorem norm_store_head_codes (guarded : Bool) :
    (program guarded)[normPc guarded 105]?=some (.scalar (.branch (.lt (.ivar 21) (.const 8)) (normPc guarded 113))) ∧
    (program guarded)[normPc guarded 106]?=some (.scalar (.index 22 (.add (.ivar 17) (.mul (.ivar 21) (.const 1024))))) ∧
    (program guarded)[normPc guarded 107]?=some (.scalar (.branch (.lt (.ivar 22) (.const 50257)) (normPc guarded 111))) ∧
    (program guarded)[normPc guarded 108]?=some (.scalar (.assign 13 (.load .local 1 (.ivar 21)))) := by
  cases guarded <;> decide

theorem norm_store_emit_codes (guarded : Bool) :
    (program guarded)[normPc guarded 109]?=some (.scalar (.index 23 (.add (.mul (.ivar 0) (.const 50257)) (.ivar 22)))) ∧
    (program guarded)[normPc guarded 110]?=some (.scalar (.store .global 0 (.ivar 23) (.un .toHalf (.bin .div (.reg 13) (.reg 12))))) ∧
    (program guarded)[normPc guarded 111]?=some (.scalar (.index 21 (.add (.ivar 21) (.const 1)))) ∧
    (program guarded)[normPc guarded 112]?=some (.scalar (.jump (normPc guarded 105))) := by
  cases guarded <;> decide

theorem norm_round_end_codes (guarded : Bool) :
    (program guarded)[normPc guarded 113]?=some (.scalar (.index 17 (.add (.ivar 17) (.const 8192)))) ∧
    (program guarded)[normPc guarded 114]?=some (.scalar (.jump 95)) ∧
    (program guarded)[normPc guarded 115]?=some (.scalar .halt) := by
  cases guarded <;> decide

#print axioms norm_pc_next
#print axioms norm_outer_codes
#print axioms norm_load_head_codes
#print axioms norm_original_clamp_code
#print axioms norm_load_body_codes
#print axioms norm_store_init_code
#print axioms norm_store_head_codes
#print axioms norm_store_emit_codes
#print axioms norm_round_end_codes
end LarkNativeSoftmax
