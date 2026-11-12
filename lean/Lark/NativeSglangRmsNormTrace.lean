import Lark.NativeSglangRmsNormGeneral
import Lark.TraceTransport

/-! Preserve arbitrary earlier trace events through the source scalar prefix. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkTraceTransport
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem set_index_append (s : State α) (tail : List Access) (t q : Nat) (v : Int) (pc : Nat) :
    LarkReduction.setIndex (appendTrace s tail) t q v pc =
      appendTrace (LarkReduction.setIndex s t q v pc) tail := rfl

theorem initialized_append (t : Nat) (s : State α) (tail : List Access) :
    initialized t (appendTrace s tail) = appendTrace (initialized t s) tail := rfl

theorem input_after_append (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) (tail : List Access) :
    inputCacheAfter input row tid iteration component t (appendTrace s tail) =
      appendTrace (inputCacheAfter input row tid iteration component t s) tail := rfl

theorem input_components_append (input : Nat → Nat → α) (row tid iteration t component remaining : Nat)
    (s : State α) (tail : List Access) :
    inputCacheComponents input row tid iteration t component remaining (appendTrace s tail) =
      appendTrace (inputCacheComponents input row tid iteration t component remaining s) tail := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih => simp only [inputCacheComponents,input_after_append,ih]

theorem input_entry_append (t : Nat) (s : State α) (tail : List Access) :
    inputCacheEntry t (appendTrace s tail) = appendTrace (inputCacheEntry t s) tail := rfl

theorem input_exit_append (iteration t : Nat) (s : State α) (tail : List Access) :
    inputCacheExit iteration t (appendTrace s tail) = appendTrace (inputCacheExit iteration t s) tail := rfl

theorem input_round_append (input : Nat → Nat → α) (row tid iteration t : Nat)
    (s : State α) (tail : List Access) :
    inputCacheRound input row tid iteration t (appendTrace s tail) =
      appendTrace (inputCacheRound input row tid iteration t s) tail := by
  simp only [inputCacheRound,input_entry_append,input_components_append,input_exit_append]

theorem input_preloads_append (input : Nat → Nat → α) (t : Nat) (s : State α) (tail : List Access) :
    inputPreloads input t (appendTrace s tail) = appendTrace (inputPreloads input t s) tail := by
  simp only [inputPreloads,initialized_append,input_round_append,advance_append]

theorem weight_after_append (input : Nat → Nat → α) (tid iteration component t : Nat)
    (s : State α) (tail : List Access) :
    weightCacheAfter input tid iteration component t (appendTrace s tail) =
      appendTrace (weightCacheAfter input tid iteration component t s) tail := rfl

theorem weight_components_append (input : Nat → Nat → α) (row tid iteration t component remaining : Nat)
    (s : State α) (tail : List Access) :
    weightCacheComponents input row tid iteration t component remaining (appendTrace s tail) =
      appendTrace (weightCacheComponents input row tid iteration t component remaining s) tail := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih => simp only [weightCacheComponents,weight_after_append,ih]

theorem weight_entry_append (t : Nat) (s : State α) (tail : List Access) :
    weightCacheEntry t (appendTrace s tail) = appendTrace (weightCacheEntry t s) tail := rfl

theorem weight_exit_append (iteration t : Nat) (s : State α) (tail : List Access) :
    weightCacheExit iteration t (appendTrace s tail) = appendTrace (weightCacheExit iteration t s) tail := rfl

theorem weight_round_append (input : Nat → Nat → α) (row tid iteration t : Nat)
    (s : State α) (tail : List Access) :
    weightCacheRound input row tid iteration t (appendTrace s tail) =
      appendTrace (weightCacheRound input row tid iteration t s) tail := by
  simp only [weightCacheRound,weight_entry_append,weight_components_append,weight_exit_append]

theorem preloads_append (input : Nat → Nat → α) (t : Nat) (s : State α) (tail : List Access) :
    preloads input t (appendTrace s tail) = appendTrace (preloads input t s) tail := by
  simp only [preloads,weightPreloads,input_preloads_append,set_index_append,weight_round_append,advance_append]

theorem sum_started_append (ops : Ops α) (t : Nat) (s : State α) (tail : List Access) :
    sumStarted ops t (appendTrace s tail) = appendTrace (sumStarted ops t s) tail := rfl

theorem pair_after_append (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) (tail : List Access) :
    pairAfter ops input row tid iteration pair t acc (appendTrace s tail) =
      appendTrace (pairAfter ops input row tid iteration pair t acc s) tail := rfl

theorem pairs_append (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α) (tail : List Access) :
    pairs ops input row tid iteration t pair remaining acc (appendTrace s tail) =
      appendTrace (pairs ops input row tid iteration t pair remaining acc s) tail := by
  induction remaining generalizing pair acc s with
  | zero => rfl
  | succ remaining ih => simp only [pairs,pair_after_append,ih]

theorem round_begin_append (t : Nat) (s : State α) (tail : List Access) :
    beginRound t (appendTrace s tail) = appendTrace (beginRound t s) tail := rfl

theorem round_end_append (t iteration : Nat) (s : State α) (tail : List Access) :
    endRound t iteration (appendTrace s tail) = appendTrace (endRound t iteration s) tail := rfl

theorem round_append (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) (tail : List Access) :
    roundAfter ops input row tid iteration t acc (appendTrace s tail) =
      appendTrace (roundAfter ops input row tid iteration t acc s) tail := by
  simp only [roundAfter,round_begin_append,pairs_append,round_end_append]

theorem prefix_append (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) (tail : List Access) :
    prefixState ops input t (appendTrace s tail) = appendTrace (prefixState ops input t s) tail := by
  simp only [prefixState,preloads_append,sum_started_append,round_append,advance_append]

/-- Execution requires read-only global data and PC0, with no prior trace premise. -/
theorem carried_prefix_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0) (reads : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s =
      some (prefixState ops input t s) := by
  let clean := {s with trace := []}
  have hc := general_prefix_run p repaired ops input t clean ht hp reads (by intro a ha; cases ha)
  have transport := run_lane_append ops (layout p) (geometry p) (program repaired) t fuel.lane clean s.trace
  have hs : appendTrace clean s.trace = s := append_empty_trace s
  rw [hs,hc] at transport
  change LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s =
    some (appendTrace (prefixState ops input t clean) s.trace) at transport
  have final : appendTrace (prefixState ops input t clean) s.trace = prefixState ops input t s := by
    rw [← prefix_append,hs]
  simpa only [final] using transport

structure PrefixData (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 44
  accumulator : s.regs t 0 = some (threadSum ops input (t / 1024) (t % 1024))
  reads : Reads p input s
  inputs : InputPrefix input (t / 1024) (t % 1024) 16 t s
  weights : WeightPrefix input (t % 1024) 16 t s

theorem carried_prefix_data (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) :
    PrefixData p ops input t (prefixState ops input t s) := by
  let clean := {s with trace := []}
  have r := general_prefix_ready p ops input t clean reads (by intro a ha; cases ha)
  have hs : appendTrace clean s.trace = s := append_empty_trace s
  rw [← hs,prefix_append]
  exact ⟨r.pc,r.accumulator,r.reads,r.inputs,r.weights⟩

theorem carried_prefix_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).trace =
      (prefixState ops input t {s with trace := []}).trace ++ s.trace := by
  have h := congrArg State.trace (prefix_append ops input t {s with trace := []} s.trace)
  rw [append_empty_trace] at h
  exact h

theorem carried_new_events_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) :
    ∀ a ∈ (prefixState ops input t {s with trace := []}).trace, Good a :=
  (general_prefix_ready p ops input t {s with trace := []} reads (by intro a ha; cases ha)).good

#print axioms initialized_append
#print axioms input_after_append
#print axioms input_components_append
#print axioms input_round_append
#print axioms input_preloads_append
#print axioms weight_after_append
#print axioms weight_components_append
#print axioms weight_round_append
#print axioms preloads_append
#print axioms sum_started_append
#print axioms pair_after_append
#print axioms pairs_append
#print axioms round_append
#print axioms prefix_append
#print axioms carried_prefix_run
#print axioms carried_prefix_data
#print axioms carried_prefix_trace
#print axioms carried_new_events_good
end LarkNativeSglangRmsNorm
