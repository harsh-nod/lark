import Lark.NativeSglangRmsNormWeightCache

/-! Induction over the actual raw-half preload loop and its two memory events.+ -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def WeightPrefix (input : Nat → Nat → α) (tid count t : Nat) (s : State α) : Prop :=
  ∀ k, k < count → s.memory (privateCell t 1 k) =
    some (input 2 (column tid (k / 8) (k % 8)))

theorem weight_cache_reads (p : Shape) (input : Nat → Nat → α)
    (_row tid iteration component t : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (weightCacheAfter input tid iteration component t s) := by
  constructor
  · intro offset hi
    rw [weight_cache_memory]
    simpa [globalCell, privateCell] using reads.1 offset hi
  · intro offset hi
    rw [weight_cache_memory]
    simpa [globalCell, privateCell] using reads.2 offset hi

theorem weight_cache_prefix (input : Nat → Nat → α) (_row tid iteration component t : Nat)
    (s : State α) (hc : component < 8)
    (cached : WeightPrefix input tid (iteration * 8 + component) t s) :
    WeightPrefix input tid (iteration * 8 + (component + 1)) t
      (weightCacheAfter input tid iteration component t s) := by
  intro k hk
  rw [weight_cache_memory]
  by_cases he : k = iteration * 8 + component
  · subst k
    have hd : (iteration * 8 + component) / 8 = iteration := by omega
    have hm : (iteration * 8 + component) % 8 = component := by omega
    simp [hd,hm]
  · have hl : privateCell t 1 k ≠ privateCell t 1 (iteration * 8 + component) := by
      intro h
      exact he (congrArg Location.offset h)
    simp only [if_neg hl]
    exact cached k (by omega)

theorem weight_cache_input_preserved (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α)
    (cached : InputPrefix input row tid 16 t s) :
    InputPrefix input row tid 16 t (weightCacheAfter input tid iteration component t s) := by
  intro k hk
  rw [weight_cache_memory]
  simpa [privateCell] using cached k hk

structure WeightCacheReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) : Prop where
  pc : s.pc t = 19
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 9 = some (iteration : Int)
  componentIndex : s.indices t 10 = some (component : Int)
  reads : Reads p input s
  inputCached : InputPrefix input row tid 16 t s
  cached : WeightPrefix input tid (iteration * 8 + component) t s
  good : ∀ a ∈ s.trace, Good a

theorem weight_cache_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (hc : component < 8)
    (ready : WeightCacheReady p input row tid iteration component t s) :
    WeightCacheReady p input row tid iteration (component + 1) t
      (weightCacheAfter input tid iteration component t s) := by
  obtain ⟨hp,h0,h1,h4,h5⟩ := weight_cache_fields input tid iteration component t s
  exact {
    pc := hp, rowIndex := h0.trans ready.rowIndex, tidIndex := h1.trans ready.tidIndex
    iterationIndex := h4.trans ready.iterationIndex, componentIndex := h5
    reads := weight_cache_reads p input row tid iteration component t s ready.reads
    inputCached := weight_cache_input_preserved input row tid iteration component t s ready.inputCached
    cached := weight_cache_prefix input row tid iteration component t s hc ready.cached
    good := weight_cache_good input tid iteration component t s ready.good }

def weightCacheComponents (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | component, remaining + 1, s =>
      weightCacheComponents input row tid iteration t (component + 1) remaining
        (weightCacheAfter input tid iteration component t s)

theorem weight_cache_components_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α)
    (hcount : component + remaining ≤ 8)
    (ready : WeightCacheReady p input row tid iteration component t s) :
    WeightCacheReady p input row tid iteration (component + remaining) t
      (weightCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => simpa only [weightCacheComponents,Nat.add_zero] using ready
  | succ remaining ih =>
      have next := weight_cache_ready p input row tid iteration component t s (by omega) ready
      have step := ih (component + 1) (weightCacheAfter input tid iteration component t s)
        (by omega) next
      simpa only [weightCacheComponents,
        show component + 1 + remaining = component + (remaining + 1) by omega] using step

theorem weight_cache_components_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid iteration t component remaining extra : Nat) (s : State α)
    (_hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2)
    (hcount : component + remaining ≤ 8)
    (ready : WeightCacheReady p input row tid iteration component t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 6 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (weightCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have hm := ready.reads.2 (column tid iteration component)
        (column_bound tid iteration component ht hi hc)
      have cycle := weight_cache_cycle p repaired ops input tid iteration component t
        (extra + 6 * remaining) s ht hi hc ready.tidIndex
        ready.iterationIndex ready.componentIndex ready.pc hm
      rewrite [show extra + 6 * (remaining + 1) = (extra + 6 * remaining) + 6 by omega, cycle]
      exact ih (component + 1) (weightCacheAfter input tid iteration component t s) (by omega)
        (weight_cache_ready p input row tid iteration component t s hc ready)

theorem weight_cache_components_epochs (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    (weightCacheComponents input row tid iteration t component remaining s).epochs = s.epochs := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      simp only [weightCacheComponents,ih,weight_cache_epochs]

theorem weight_cache_components_trace_length (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    (weightCacheComponents input row tid iteration t component remaining s).trace.length =
      s.trace.length + 2 * remaining := by
  induction remaining generalizing component s with
  | zero => simp [weightCacheComponents]
  | succ remaining ih =>
      simp only [weightCacheComponents,ih,weight_cache_trace,List.length_cons]
      omega

#print axioms weight_cache_reads
#print axioms weight_cache_prefix
#print axioms weight_cache_input_preserved
#print axioms weight_cache_ready
#print axioms weight_cache_components_ready
#print axioms weight_cache_components_eq
#print axioms weight_cache_components_epochs
#print axioms weight_cache_components_trace_length
end LarkNativeSglangRmsNorm
