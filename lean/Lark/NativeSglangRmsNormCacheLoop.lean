import Lark.NativeSglangRmsNormCache

/-! Induction over the actual raw-half preload loop and its two memory events.+ -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ offset, offset < p.rows * 16384 → s.memory (globalCell 1 offset) = some (input 1 offset)) ∧
  (∀ offset, offset < 16384 → s.memory (globalCell 2 offset) = some (input 2 offset))

def InputPrefix (input : Nat → Nat → α) (row tid count t : Nat) (s : State α) : Prop :=
  ∀ k, k < count → s.memory (privateCell t 0 k) =
    some (input 1 (address row (column tid (k / 8) (k % 8))))

theorem initial_reads (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (initial p input outside) :=
  ⟨initial_input p input outside,initial_weight p input outside⟩

theorem input_cache_reads (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (inputCacheAfter input row tid iteration component t s) := by
  constructor
  · intro offset hi
    rw [input_cache_memory]
    simpa [globalCell, privateCell] using reads.1 offset hi
  · intro offset hi
    rw [input_cache_memory]
    simpa [globalCell, privateCell] using reads.2 offset hi

theorem input_cache_prefix (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) (hc : component < 8)
    (cached : InputPrefix input row tid (iteration * 8 + component) t s) :
    InputPrefix input row tid (iteration * 8 + (component + 1)) t
      (inputCacheAfter input row tid iteration component t s) := by
  intro k hk
  rw [input_cache_memory]
  by_cases he : k = iteration * 8 + component
  · subst k
    have hd : (iteration * 8 + component) / 8 = iteration := by omega
    have hm : (iteration * 8 + component) % 8 = component := by omega
    simp [hd,hm]
  · have hl : privateCell t 0 k ≠ privateCell t 0 (iteration * 8 + component) := by
      intro h
      exact he (congrArg Location.offset h)
    simp only [if_neg hl]
    exact cached k (by omega)

structure InputCacheReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) : Prop where
  pc : s.pc t = 7
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 4 = some (iteration : Int)
  componentIndex : s.indices t 5 = some (component : Int)
  reads : Reads p input s
  cached : InputPrefix input row tid (iteration * 8 + component) t s
  good : ∀ a ∈ s.trace, Good a

theorem input_cache_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (hc : component < 8)
    (ready : InputCacheReady p input row tid iteration component t s) :
    InputCacheReady p input row tid iteration (component + 1) t
      (inputCacheAfter input row tid iteration component t s) := by
  obtain ⟨hp,h0,h1,h4,h5⟩ := input_cache_fields input row tid iteration component t s
  exact {
    pc := hp, rowIndex := h0.trans ready.rowIndex, tidIndex := h1.trans ready.tidIndex
    iterationIndex := h4.trans ready.iterationIndex, componentIndex := h5
    reads := input_cache_reads p input row tid iteration component t s ready.reads
    cached := input_cache_prefix input row tid iteration component t s hc ready.cached
    good := input_cache_good input row tid iteration component t s ready.good }

def inputCacheComponents (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | component, remaining + 1, s =>
      inputCacheComponents input row tid iteration t (component + 1) remaining
        (inputCacheAfter input row tid iteration component t s)

theorem input_cache_components_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α)
    (hcount : component + remaining ≤ 8)
    (ready : InputCacheReady p input row tid iteration component t s) :
    InputCacheReady p input row tid iteration (component + remaining) t
      (inputCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => simpa only [inputCacheComponents,Nat.add_zero] using ready
  | succ remaining ih =>
      have next := input_cache_ready p input row tid iteration component t s (by omega) ready
      have step := ih (component + 1) (inputCacheAfter input row tid iteration component t s)
        (by omega) next
      simpa only [inputCacheComponents,
        show component + 1 + remaining = component + (remaining + 1) by omega] using step

theorem input_cache_components_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid iteration t component remaining extra : Nat) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2)
    (hcount : component + remaining ≤ 8)
    (ready : InputCacheReady p input row tid iteration component t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 7 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (inputCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have hm := ready.reads.1 (address row (column tid iteration component))
        (address_bound p row tid iteration component hr ht hi hc)
      have cycle := input_cache_cycle p repaired ops input row tid iteration component t
        (extra + 7 * remaining) s hr ht hi hc ready.rowIndex ready.tidIndex
        ready.iterationIndex ready.componentIndex ready.pc hm
      rewrite [show extra + 7 * (remaining + 1) = (extra + 7 * remaining) + 7 by omega, cycle]
      exact ih (component + 1) (inputCacheAfter input row tid iteration component t s) (by omega)
        (input_cache_ready p input row tid iteration component t s hc ready)

theorem input_cache_components_epochs (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    (inputCacheComponents input row tid iteration t component remaining s).epochs = s.epochs := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      simp only [inputCacheComponents,ih,input_cache_epochs]

theorem input_cache_components_trace_length (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    (inputCacheComponents input row tid iteration t component remaining s).trace.length =
      s.trace.length + 2 * remaining := by
  induction remaining generalizing component s with
  | zero => simp [inputCacheComponents]
  | succ remaining ih =>
      simp only [inputCacheComponents,ih,input_cache_trace,List.length_cons]
      omega

#print axioms initial_reads
#print axioms input_cache_reads
#print axioms input_cache_prefix
#print axioms input_cache_ready
#print axioms input_cache_components_ready
#print axioms input_cache_components_eq
#print axioms input_cache_components_epochs
#print axioms input_cache_components_trace_length
end LarkNativeSglangRmsNorm
