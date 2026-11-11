import Lark.NativeFusedRmsNormOutputComponent

/-! Counted output components with preserved shared values/weights and retained
previous output stores. No arithmetic identities or race-freedom hypotheses.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def OutputCompleted (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (inverse : α) (ordinal : Nat) (s : State α) : Prop :=
  ∀ j, j < ordinal → s.memory (globalCell 0 (flatAddress row tid j)) =
    some (ops.toHalf (outputWeighted ops input row (slot tid j) inverse))

theorem output_component_completed (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (hi : iteration < 2) (hc : component < 8)
    (done : OutputCompleted ops input row tid inverse (iteration * 8 + component) s) :
    OutputCompleted ops input row tid inverse (iteration * 8 + component + 1)
      (outputComponent ops input row tid iteration component t inverse s) := by
  intro j hj
  by_cases heq : j = iteration * 8 + component
  · subst j
    simpa only [flatAddress, slot_rank tid iteration component hc] using
      output_component_value ops input row tid iteration component t inverse s
  · have hlt : j < iteration * 8 + component := by omega
    have ha : flatAddress row tid j ≠ address row (column tid iteration component) := by
      intro he
      have he' : flatAddress row tid j = flatAddress row tid (iteration * 8 + component) := by
        simpa only [flatAddress, slot_rank tid iteration component hc] using he
      exact heq (flat_address_injective row tid j (iteration * 8 + component) (by omega) (by omega) he')
    simpa [output_component_memory, globalCell, ha] using done j hlt

structure OutputReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t = 58
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 8 = some (iteration : Int)
  componentIndex : s.indices t 9 = some (component : Int)
  scale : s.regs t 8 = some inverse
  reads : OutputReads ops input row s
  completed : OutputCompleted ops input row tid inverse (iteration * 8 + component) s
  good : ∀ a ∈ s.trace, Good a

theorem output_component_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) (he : t = row * 1024 + tid)
    (ready : OutputReady ops input row tid iteration component t inverse s) :
    OutputReady ops input row tid iteration (component + 1) t inverse
      (outputComponent ops input row tid iteration component t inverse s) := by
  obtain ⟨hp,h0,h1,h8,h9,hx⟩ := output_component_fields ops input row tid iteration component t inverse s
  exact {
    pc := hp
    rowIndex := h0.trans ready.rowIndex
    tidIndex := h1.trans ready.tidIndex
    iterationIndex := h8.trans ready.iterationIndex
    componentIndex := h9
    scale := hx.trans ready.scale
    reads := output_component_reads ops input row tid iteration component t inverse s ready.reads
    completed := by
      simpa only [Nat.add_assoc] using output_component_completed ops input row tid iteration component t inverse s hi hc ready.completed
    good := output_component_good p ops input row tid iteration component t inverse s ht hi hc he ready.good }

def outputComponents (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) (inverse : α) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | component, remaining + 1, s =>
      outputComponents ops input row tid iteration t inverse (component + 1) remaining
        (outputComponent ops input row tid iteration component t inverse s)

theorem output_components_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (hcount : component + remaining ≤ 8)
    (ready : OutputReady ops input row tid iteration component t inverse s) :
    OutputReady ops input row tid iteration (component + remaining) t inverse
      (outputComponents ops input row tid iteration t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => simpa only [outputComponents, Nat.add_zero] using ready
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have next := output_component_ready p ops input row tid iteration component t inverse s ht hi hc he ready
      have step := ih (component + 1) (outputComponent ops input row tid iteration component t inverse s) (by omega) next
      simpa only [outputComponents, show component + 1 + remaining = component + (remaining + 1) by omega] using step

theorem output_components_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining extra : Nat) (inverse : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (hcount : component + remaining ≤ 8)
    (ready : OutputReady ops input row tid iteration component t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 11 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (outputComponents ops input row tid iteration t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have cycle := output_component_cycle p ops input row tid iteration component t (extra + 11 * remaining)
        inverse s hr ht hi hc he ready.reads ready.rowIndex ready.tidIndex ready.iterationIndex ready.componentIndex ready.scale ready.pc
      rewrite [show extra + 11 * (remaining + 1) = (extra + 11 * remaining) + 11 by omega, cycle]
      exact ih (component + 1) (outputComponent ops input row tid iteration component t inverse s) (by omega)
        (output_component_ready p ops input row tid iteration component t inverse s ht hi hc he ready)

theorem output_components_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) :
    (outputComponents ops input row tid iteration t inverse component remaining s).trace.length =
      s.trace.length + 3 * remaining := by
  induction remaining generalizing component s with
  | zero => simp [outputComponents]
  | succ remaining ih =>
      simp only [outputComponents, ih, output_component_trace, List.length_cons]
      omega

#print axioms output_component_completed
#print axioms output_component_ready
#print axioms output_components_ready
#print axioms output_components_eq
#print axioms output_components_trace_length
end LarkNativeFusedRmsNorm
