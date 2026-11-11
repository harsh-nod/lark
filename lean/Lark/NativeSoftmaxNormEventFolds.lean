import Lark.NativeSoftmaxNormComponentMembers

/-! Membership transport through the actual normalization round and scheduler
folds. An event depends only on the preserved epoch map; later accesses cannot
erase it. The concrete reader/writer witnesses will instantiate these lemmas. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_rounds_event_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration count target : Nat) (event : (Nat → Epoch) → Access)
    (s : State α) (hlo : iteration≤target) (hhi : target<iteration+count)
    (hit : ∀ state : State α, event state.epochs ∈ (normRoundState guarded ops input row tid target state).trace) :
    event s.epochs ∈ (normRounds guarded ops input row tid iteration count s).trace := by
  induction count generalizing iteration s with
  | zero => omega
  | succ count ih =>
    let head := normRoundState guarded ops input row tid iteration s
    change event s.epochs ∈ (normRounds guarded ops input row tid (iteration+1) count head).trace
    by_cases he : target=iteration
    · subst target
      exact norm_rounds_trace_grows guarded ops input row tid (iteration+1) count head _ (hit s)
    · have hm := ih (iteration+1) head (by omega) (by omega)
      simpa only [head,norm_round_epochs] using hm

theorem norm_scheduler_fold_trace_grows (step : Nat → State α → State α) (ts : List Nat)
    (growth : ∀ t s, NormTraceGrows s (step t s)) (s : State α) :
    NormTraceGrows s (ts.foldl (fun state t => step t state) s) := by
  induction ts generalizing s with
  | nil => exact fun _ ha => ha
  | cons t ts ih => exact norm_trace_grows_trans s _ _ (growth t s) (ih _)

theorem norm_scheduler_fold_event_member (step : Nat → State α → State α)
    (ts : List Nat) (target : Nat) (event : (Nat → Epoch) → Access)
    (growth : ∀ t s, NormTraceGrows s (step t s))
    (epochs : ∀ t s, (step t s).epochs=s.epochs)
    (hit : ∀ state : State α, event state.epochs ∈ (step target state).trace)
    (s : State α) (ht : target∈ts) :
    event s.epochs ∈ (ts.foldl (fun state t => step t state) s).trace := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons t ts ih =>
    change event s.epochs ∈ (ts.foldl (fun state t => step t state) (step t s)).trace
    rcases List.mem_cons.mp ht with he | hm
    · subst target
      exact norm_scheduler_fold_trace_grows step ts growth (step t s) _ (hit s)
    · have hm := ih (step t s) hm
      simpa only [epochs] using hm

#print axioms norm_rounds_event_member
#print axioms norm_scheduler_fold_trace_grows
#print axioms norm_scheduler_fold_event_member
end LarkNativeSoftmax
