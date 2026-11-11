import Lark.NativeFusedRmsNormComponent

/-! Loop induction with separate invariants for already stored and unread
residual cells. This permits actual in-place execution without a read-only fiction.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def flatAdded (ops : Ops α) (input : Nat → Nat → α) (row tid ordinal : Nat) : α :=
  ops.add (ops.fromHalf (input 0 (flatAddress row tid ordinal)))
    (ops.fromHalf (input 1 (flatAddress row tid ordinal)))

def Completed (ops : Ops α) (input : Nat → Nat → α) (row tid t ordinal : Nat) (s : State α) : Prop :=
  ∀ j, j < ordinal →
    s.memory (globalCell 1 (flatAddress row tid j)) = some (ops.toHalf (flatAdded ops input row tid j)) ∧
    s.memory (unroundedCell t (slot tid j)) = some (flatAdded ops input row tid j)

theorem component_completed (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (hi : iteration < 2) (hc : component < 8)
    (done : Completed ops input row tid t (iteration * 8 + component) s) :
    Completed ops input row tid t (iteration * 8 + component + 1)
      (componentAfter ops input row tid iteration component t acc s) := by
  intro j hj
  by_cases heq : j = iteration * 8 + component
  · subst j
    simpa only [flatAdded, flatAddress, slot_rank tid iteration component hc, added]
      using component_values ops input row tid iteration component t acc s
  · have hlt : j < iteration * 8 + component := by omega
    have old := done j hlt
    have ha : flatAddress row tid j ≠ address row (column tid iteration component) := by
      intro he
      have he' : flatAddress row tid j = flatAddress row tid (iteration * 8 + component) := by
        simpa only [flatAddress, slot_rank tid iteration component hc] using he
      exact heq (flat_address_injective row tid j (iteration * 8 + component) (by omega) (by omega) he')
    have hs : slot tid j ≠ column tid iteration component := by
      intro he
      exact ha (congrArg (address row) he)
    constructor
    · simpa [component_memory, globalCell, unroundedCell, ha] using old.1
    · simpa [component_memory, globalCell, unroundedCell, hs] using old.2

structure Ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 9
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  iterationIndex : s.indices t 4 = some (iteration : Int)
  componentIndex : s.indices t 5 = some (component : Int)
  accumulator : s.regs t 0 = some acc
  pending : Pending input row tid (iteration * 8 + component) s
  completed : Completed ops input row tid t (iteration * 8 + component) s
  good : ∀ a ∈ s.trace, Good a

theorem component_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) (he : t = row * 1024 + tid)
    (ready : Ready ops input row tid iteration component t acc s) :
    Ready ops input row tid iteration (component + 1) t
      (ops.add acc (squared ops input row tid iteration component))
      (componentAfter ops input row tid iteration component t acc s) := by
  obtain ⟨hp, h0, h1, h4, h5, ha⟩ := component_fields ops input row tid iteration component t acc s
  exact {
    pc := hp
    rowIndex := h0.trans ready.rowIndex
    tidIndex := h1.trans ready.tidIndex
    iterationIndex := h4.trans ready.iterationIndex
    componentIndex := h5
    accumulator := ha
    pending := by
      simpa only [Nat.add_assoc] using component_pending ops input row tid iteration component t acc s hi hc ready.pending
    completed := by
      simpa only [Nat.add_assoc] using component_completed ops input row tid iteration component t acc s hi hc ready.completed
    good := component_good p ops input row tid iteration component t acc s ht hi hc he ready.good }

def components (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → α → State α → State α
  | _, 0, _, s => s
  | component, remaining + 1, acc, s =>
      components ops input row tid iteration t (component + 1) remaining
        (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)

theorem components_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (hcount : component + remaining ≤ 8)
    (ready : Ready ops input row tid iteration component t acc s) :
    Ready ops input row tid iteration (component + remaining) t
      (folded ops input row tid iteration component remaining acc)
      (components ops input row tid iteration t component remaining acc s) := by
  induction remaining generalizing component acc s with
  | zero => simpa only [components, folded, Nat.add_zero] using ready
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have next := component_ready p ops input row tid iteration component t acc s ht hi hc he ready
      have step := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s) (by omega) next
      simpa only [components, folded,
        show component + 1 + remaining = component + (remaining + 1) by omega] using step

theorem components_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (hcount : component + remaining ≤ 8)
    (ready : Ready ops input row tid iteration component t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 12 * remaining) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (components ops input row tid iteration t component remaining acc s) := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      have hc : component < 8 := by omega
      have hk : iteration * 8 + component < 16 := by omega
      have m0 := ready.pending.1 (iteration * 8 + component) hk
      have m1 := ready.pending.2 (iteration * 8 + component) (Nat.le_refl _) hk
      simp only [flatAddress, slot_rank tid iteration component hc] at m0 m1
      have cycle := component_cycle p ops input row tid iteration component t (extra + 12 * remaining)
        acc s hr ht hi hc ready.rowIndex ready.tidIndex ready.iterationIndex ready.componentIndex
        ready.accumulator ready.pc m0 m1
      rewrite [show extra + 12 * (remaining + 1) = (extra + 12 * remaining) + 12 by omega, cycle]
      exact ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s) (by omega)
        (component_ready p ops input row tid iteration component t acc s ht hi hc he ready)

theorem components_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α) :
    (components ops input row tid iteration t component remaining acc s).trace.length =
      s.trace.length + 4 * remaining := by
  induction remaining generalizing component acc s with
  | zero => simp [components]
  | succ remaining ih =>
      simp only [components, ih, component_trace, List.length_cons]
      omega

#print axioms component_completed
#print axioms component_ready
#print axioms components_ready
#print axioms components_eq
#print axioms components_trace_length
end LarkNativeFusedRmsNorm
