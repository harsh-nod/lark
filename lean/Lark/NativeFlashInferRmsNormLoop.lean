import Lark.NativeFlashInferRmsNormComponent

/-! The source's eight-component counted loop, with unchanged input memory. -/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 9
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 4 = some (iteration : Int)
  componentIndex : s.indices t 5 = some (component : Int)
  accumulator : s.regs t 0 = some acc
  inputReady : InputReady input row tid s
  good : ∀ a ∈ s.trace, Good a

theorem component_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ready : Ready ops input row tid iteration component t acc s) :
    Ready ops input row tid iteration (component + 1) t
      (ops.add acc (squared ops input row tid iteration component))
      (componentAfter ops input row tid iteration component t acc s) := by
  obtain ⟨hp, h0, h1, h4, h5, ha⟩ := component_fields ops input row tid iteration component t acc s
  exact {
    pc := hp, rowIndex := h0.trans ready.rowIndex, tidIndex := h1.trans ready.tidIndex
    iterationIndex := h4.trans ready.iterationIndex, componentIndex := h5, accumulator := ha
    inputReady := ready.inputReady
    good := component_good ops input row tid iteration component t acc s ready.good }

def components (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => s
  | component, remaining + 1, acc, s =>
      components ops input row tid iteration t (component + 1) remaining
        (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)

theorem components_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α)
    (ready : Ready ops input row tid iteration component t acc s) :
    Ready ops input row tid iteration (component + remaining) t
      (folded ops input row tid iteration component remaining acc)
      (components ops input row tid iteration t component remaining acc s) := by
  induction remaining generalizing component acc s with
  | zero => simpa only [components, folded, Nat.add_zero] using ready
  | succ remaining ih =>
      have next := component_ready ops input row tid iteration component t acc s ready
      have step := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s) next
      simpa only [components, folded,
        show component + 1 + remaining = component + (remaining + 1) by omega] using step

theorem components_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2)
    (hcount : component + remaining ≤ 8)
    (ready : Ready ops input row tid iteration component t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (components ops input row tid iteration t component remaining acc s) := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have hk : iteration * 8 + component < 16 := by omega
      have hm := ready.inputReady (iteration * 8 + component) hk
      simp only [flatAddress, slot_rank tid iteration component hc] at hm
      have cycle := component_cycle p ops input row tid iteration component t (extra + 8 * remaining)
        acc s hr ht hi hc ready.rowIndex ready.tidIndex ready.iterationIndex ready.componentIndex
        ready.accumulator ready.pc hm
      rewrite [show extra + 8 * (remaining + 1) = (extra + 8 * remaining) + 8 by omega, cycle]
      exact ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s) (by omega)
        (component_ready ops input row tid iteration component t acc s ready)

theorem components_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α) :
    (components ops input row tid iteration t component remaining acc s).memory = s.memory := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)
      simpa only [components, component_memory] using h

theorem components_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α) :
    (components ops input row tid iteration t component remaining acc s).epochs = s.epochs := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      have h := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)
      simpa only [components, component_epochs] using h

theorem components_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α) :
    (components ops input row tid iteration t component remaining acc s).trace.length =
      s.trace.length + remaining := by
  induction remaining generalizing component acc s with
  | zero => simp [components]
  | succ remaining ih =>
      simp only [components, ih, component_trace, List.length_cons]
      omega

#print axioms component_ready
#print axioms components_ready
#print axioms components_eq
#print axioms components_memory
#print axioms components_epochs
#print axioms components_trace_length
end LarkNativeFlashInferRmsNorm
