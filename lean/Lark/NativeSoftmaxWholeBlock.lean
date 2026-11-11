import Lark.NativeSoftmaxNormBlockCounts
import Lark.NativeSoftmaxReductionPrefix

/-! Constructive execution of all five actual block phases from PC0 to halt.
Both full bound sources retain the original machine, native64 scheduler and
fuel. All converted normalization outputs are explicit. The repaired block
has a proved race-free actual trace. Grid composition, original conflict
reachability and canonical-real/IEEE equivalence remain separate obligations. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def wholeBlock (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : State α := normBlock guarded ops input row (sumState p ops input row s)

theorem whole_block_norm_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    NormBlockEntry p ops input row (sumState p ops input row s) :=
  norm_block_entry_of_sum p ops input row _ (sum_ready p ops input row s entry) (sum_state_outputs p ops input row s)

theorem whole_block_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block s=
      some (wholeBlock p guarded ops input row s) := by
  have h := sum_block_eq p guarded ops input row 1 s entry
  change LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block s=_ at h
  rewrite [h]
  exact norm_block_run p guarded ops input row 0 _ (whole_block_norm_entry p ops input row s entry)

theorem whole_block_pc (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (wholeBlock p guarded ops input row s).pc (row*1024+tid)=normPc guarded 115 :=
  norm_block_pc guarded ops input row tid _ ht

theorem whole_block_outputs (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : NormOutputRow ops input row (wholeBlock p guarded ops input row s) :=
  norm_block_outputs guarded ops input row _

theorem whole_block_normalization_epochs (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (wholeBlock p guarded ops input row s).epochs=(sumState p ops input row s).epochs :=
  norm_block_epochs guarded ops input row _

theorem whole_block_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    ∀ a ∈ (wholeBlock p true ops input row s).trace, Good a :=
  norm_block_fixed_good p ops input row _ (whole_block_norm_entry p ops input row s entry) (sum_ready p ops input row s entry).good

theorem whole_block_fixed_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    raceFree (geometry p) (wholeBlock p true ops input row s).trace=true :=
  race_free p _ (whole_block_fixed_good p ops input row s entry)

theorem sum_state_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (sumState p ops input row s).trace.length=s.trace.length+273700 := by
  dsimp only [sumState]
  rewrite [after_sum_trace_length,after_exp_trace_length,maximum_trace_length]
  omega

theorem whole_block_count_join (guarded : Bool) (before middle after : State α)
    (hm : middle.trace.length=before.trace.length+273700)
    (ha : after.trace.length=middle.trace.length+(if guarded then 202052 else 216226)) :
    after.trace.length=before.trace.length+(if guarded then 475752 else 489926) := by
  cases guarded with
  | false =>
    change after.trace.length=middle.trace.length+216226 at ha
    change after.trace.length=before.trace.length+489926
    omega
  | true =>
    change after.trace.length=middle.trace.length+202052 at ha
    change after.trace.length=before.trace.length+475752
    omega

theorem whole_block_trace_length (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    (wholeBlock p guarded ops input row s).trace.length=s.trace.length+(if guarded then 475752 else 489926) :=
  whole_block_count_join guarded s (sumState p ops input row s) (wholeBlock p guarded ops input row s)
    (sum_state_trace_length p ops input row s) (norm_block_trace_length guarded ops input row _)

theorem initial_whole_block (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row fuel.block (initial (layout p) input outside)=
      some (wholeBlock p guarded ops input row (initial (layout p) input outside)) :=
  whole_block_run p guarded ops input row _ (initial_block_entry p input outside row hr)

theorem initial_whole_block_outputs (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    NormOutputRow ops input row (wholeBlock p guarded ops input row (initial (layout p) input outside)) :=
  whole_block_outputs p guarded ops input row _

theorem initial_whole_block_fixed_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    raceFree (geometry p) (wholeBlock p true ops input row (initial (layout p) input outside)).trace=true :=
  whole_block_fixed_race_free p ops input row _ (initial_block_entry p input outside row hr)

theorem initial_whole_block_trace_length (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (wholeBlock p guarded ops input row (initial (layout p) input outside)).trace.length=(if guarded then 475752 else 489926) :=
  exp_trace_length_of_nil (initial (layout p) input outside)
    (wholeBlock p guarded ops input row (initial (layout p) input outside)) _ rfl (whole_block_trace_length p guarded ops input row _)

#print axioms whole_block_norm_entry
#print axioms whole_block_run
#print axioms whole_block_pc
#print axioms whole_block_outputs
#print axioms whole_block_normalization_epochs
#print axioms whole_block_fixed_good
#print axioms whole_block_fixed_race_free
#print axioms sum_state_trace_length
#print axioms whole_block_count_join
#print axioms whole_block_trace_length
#print axioms initial_whole_block
#print axioms initial_whole_block_outputs
#print axioms initial_whole_block_fixed_race_free
#print axioms initial_whole_block_trace_length
end LarkNativeSoftmax
