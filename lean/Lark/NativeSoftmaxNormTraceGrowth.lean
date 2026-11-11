import Lark.NativeSoftmaxWholeBlock

/-! Normalization only prepends accesses. These facts apply to both actual
source variants and arbitrary scalar operations, inputs and starting states.
They let a witnessed component access survive every later scheduler fold. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormTraceGrows (before after : State α) : Prop :=
  ∀ a, a∈before.trace → a∈after.trace

theorem norm_trace_grows_trans (s t u : State α)
    (h : NormTraceGrows s t) (k : NormTraceGrows t u) : NormTraceGrows s u :=
  fun a ha => k a (h a ha)

theorem norm_load_trace_grows (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    NormTraceGrows s (normLoadState guarded ops row tid iteration component t s) := by
  intro a ha
  rewrite [norm_load_component_trace]
  split <;> simp [ha]

theorem norm_store_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    NormTraceGrows s (normStoreAfter guarded ops input row tid iteration component s) := by
  intro a ha
  rewrite [norm_store_component_trace]
  split <;> simp [ha]

theorem norm_loads_trace_grows (guarded : Bool) (ops : Ops α)
    (row tid iteration component count : Nat) (s : State α) :
    NormTraceGrows s (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => exact fun _ ha => ha
  | succ count ih =>
    exact norm_trace_grows_trans s _ _
      (norm_load_trace_grows guarded ops row tid iteration component (row*1024+tid) s)
      (ih (component+1) _)

theorem norm_stores_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) :
    NormTraceGrows s (normStores guarded ops input row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => exact fun _ ha => ha
  | succ count ih =>
    exact norm_trace_grows_trans s _ _
      (norm_store_trace_grows guarded ops input row tid iteration component s)
      (ih (component+1) _)

theorem norm_buffer_trace_grows (guarded : Bool) (ops : Ops α)
    (row tid iteration : Nat) (s : State α) :
    NormTraceGrows s (normBufferState guarded ops row tid iteration s) := by
  intro a ha
  change a∈(normLoads guarded ops row tid iteration 0 8 (normLoadBegin (row*1024+tid) s)).trace
  exact norm_loads_trace_grows guarded ops row tid iteration 0 8 _ a ha

theorem norm_round_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) :
    NormTraceGrows s (normRoundState guarded ops input row tid iteration s) := by
  intro a ha
  change a∈(normStores guarded ops input row tid iteration 0 8 (normBufferState guarded ops row tid iteration s)).trace
  exact norm_stores_trace_grows guarded ops input row tid iteration 0 8 _ a
    (norm_buffer_trace_grows guarded ops row tid iteration s a ha)

theorem norm_rounds_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count : Nat) (s : State α) :
    NormTraceGrows s (normRounds guarded ops input row tid iteration count s) := by
  induction count generalizing iteration s with
  | zero => exact fun _ ha => ha
  | succ count ih =>
    exact norm_trace_grows_trans s _ _ (norm_round_trace_grows guarded ops input row tid iteration s)
      (ih (iteration+1) _)

theorem norm_sequence_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid count : Nat) (s : State α) :
    NormTraceGrows s (normExit guarded (row*1024+tid)
      (normRounds guarded ops input row tid 0 count (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s))) := by
  intro a ha
  simp only [normExit,advance]
  apply norm_rounds_trace_grows guarded ops input row tid 0 count
    (normStart ops (rowExpSum ops input row) (row*1024+tid) tid s) a
  rewrite [(norm_start_frames ops (rowExpSum ops input row) (row*1024+tid) tid s).2.2]
  exact List.mem_cons_of_mem _ ha

theorem norm_lane_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) :
    NormTraceGrows s (normLaneState guarded ops input row tid s) :=
  norm_sequence_trace_grows guarded ops input row tid 7 s

theorem norm_scalar_fold_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) :
    NormTraceGrows s (normScalarFold guarded ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact fun _ ha => ha
  | cons t ts ih =>
    exact norm_trace_grows_trans s _ _
      (norm_lane_trace_grows guarded ops input row (t%1024) s) (ih _)

theorem norm_wave_fold_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) :
    NormTraceGrows s (normWaveFold guarded ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact fun _ ha => ha
  | cons w ws ih =>
    exact norm_trace_grows_trans s _ _
      (norm_scalar_fold_trace_grows guarded ops input row (cohortThreads row w 64) s) (ih _)

theorem norm_block_trace_grows (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : NormTraceGrows s (normBlock guarded ops input row s) :=
  norm_wave_fold_trace_grows guarded ops input row (List.range 16) s

#print axioms norm_trace_grows_trans
#print axioms norm_load_trace_grows
#print axioms norm_store_trace_grows
#print axioms norm_loads_trace_grows
#print axioms norm_stores_trace_grows
#print axioms norm_buffer_trace_grows
#print axioms norm_round_trace_grows
#print axioms norm_rounds_trace_grows
#print axioms norm_sequence_trace_grows
#print axioms norm_lane_trace_grows
#print axioms norm_scalar_fold_trace_grows
#print axioms norm_wave_fold_trace_grows
#print axioms norm_block_trace_grows
end LarkNativeSoftmax
