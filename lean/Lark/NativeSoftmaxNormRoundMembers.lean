import Lark.NativeSoftmaxNormEventFolds

/-! The original load buffer and complete outer round contain each selected
read, and every valid write. Symbolic loop bounds keep the proof compositional;
the actual eight-component source loops are then direct specializations. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_buffer_prefix_original_member (ops : Ops α) (row tid iteration count component : Nat)
    (s : State α) (hc : component<count) :
    normReadAccess row tid iteration component s.epochs ∈
      (normLoadFinish false (row*1024+tid)
        (normLoads false ops row tid iteration 0 count (normLoadBegin (row*1024+tid) s))).trace := by
  have hm := norm_loads_original_member ops row tid iteration 0 count component
    (normLoadBegin (row*1024+tid) s) (by omega) (by omega)
  simpa only [normLoadFinish,normLoadBegin,setIndex,advance] using hm

theorem norm_buffer_original_member (ops : Ops α) (row tid iteration component : Nat)
    (s : State α) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈ (normBufferState false ops row tid iteration s).trace :=
  norm_buffer_prefix_original_member ops row tid iteration 8 component s hc

theorem norm_round_prefix_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count component : Nat) (s : State α) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈
      (normStoreFinish false (row*1024+tid) tid iteration
        (normStores false ops input row tid iteration 0 count (normBufferState false ops row tid iteration s))).trace := by
  have hm := norm_stores_trace_grows false ops input row tid iteration 0 count
    (normBufferState false ops row tid iteration s) _ (norm_buffer_original_member ops row tid iteration component s hc)
  simpa only [normStoreFinish,setIndex,advance] using hm

theorem norm_round_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈ (normRoundState false ops input row tid iteration s).trace :=
  norm_round_prefix_original_member ops input row tid iteration 8 component s hc

theorem norm_round_prefix_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count component : Nat) (s : State α)
    (hc : component<count) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈
      (normStoreFinish guarded (row*1024+tid) tid iteration
        (normStores guarded ops input row tid iteration 0 count (normBufferState guarded ops row tid iteration s))).trace := by
  have hm := norm_stores_valid_member guarded ops input row tid iteration 0 count component
    (normBufferState guarded ops row tid iteration s) (by omega) (by omega) hcol
  simpa only [normStoreFinish,setIndex,advance,norm_buffer_epochs] using hm

theorem norm_round_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (hc : component<8) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈ (normRoundState guarded ops input row tid iteration s).trace :=
  norm_round_prefix_valid_member guarded ops input row tid iteration 8 component s hc hcol

#print axioms norm_buffer_prefix_original_member
#print axioms norm_buffer_original_member
#print axioms norm_round_prefix_original_member
#print axioms norm_round_original_member
#print axioms norm_round_prefix_valid_member
#print axioms norm_round_valid_member
end LarkNativeSoftmax
