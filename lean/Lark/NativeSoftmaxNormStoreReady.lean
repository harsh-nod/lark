import Lark.NativeSoftmaxNormStoreComponent

/-! Value and frame invariants of actual normalization stores. Writes preserve
the private buffer and all later outer rounds' exponential inputs. Earlier
components keep their normalized outputs while later components execute. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormOutputs (ops : Ops α) (input : Nat → Nat → α) (row tid iteration upto : Nat) (s : State α) : Prop :=
  ∀ component, component<upto → column tid iteration component<50257 →
    s.memory (globalCell 0 (address row (column tid iteration component)))=
      some (normOutputValue ops input row (column tid iteration component))

theorem norm_store_component_memory_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (l : Location)
    (hl : l ≠ globalCell 0 (address row (column tid iteration component))) :
    (normStoreAfter guarded ops input row tid iteration component s).memory l=s.memory l := by
  rewrite [norm_store_component_memory]
  split <;> simp [hl]

theorem norm_store_component_buffered (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component upto : Nat) (s : State α) (hb : NormBuffered ops input row tid iteration upto s) :
    NormBuffered ops input row tid iteration upto (normStoreAfter guarded ops input row tid iteration component s) := by
  intro c hc hcol
  rewrite [norm_store_component_memory_other guarded ops input row tid iteration component s _ (by
    intro he
    have hs := congrArg Location.space he
    simp [localCell,globalCell] at hs)]
  exact hb c hc hcol

theorem norm_store_component_present (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hp : NormPresent row s) :
    NormPresent row (normStoreAfter guarded ops input row tid iteration component s) := by
  intro c hc
  rewrite [norm_store_component_memory]
  split
  · split
    · exact ⟨_,rfl⟩
    · exact hp c hc
  · exact hp c hc

theorem norm_store_component_future (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hc : component<8)
    (hf : NormFuture ops input row tid (iteration+1) s) :
    NormFuture ops input row tid (iteration+1) (normStoreAfter guarded ops input row tid iteration component s) := by
  intro it hi hib c hcb hcol
  rewrite [norm_store_component_memory_other guarded ops input row tid iteration component s _ (by
    intro he
    have ho := congrArg Location.offset he
    change address row (column tid it c)=address row (column tid iteration component) at ho
    unfold address column at ho
    omega)]
  exact hf it hi hib c hcb hcol

theorem norm_store_component_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hc : component<8)
    (ready : NormStoreReady p guarded ops input row tid iteration component s) :
    NormStoreReady p guarded ops input row tid iteration (component+1)
      (normStoreAfter guarded ops input row tid iteration component s) := by
  have fields := norm_store_component_fields guarded ops input row tid iteration component s
  have idx := norm_store_component_index_other guarded ops input row tid iteration component
  exact {
    valid := ready.valid
    bound := ready.bound
    pc := fields.1
    native := ⟨(idx 0 s (by decide) (by decide) (by decide)).trans ready.native.1,
      (idx 1 s (by decide) (by decide) (by decide)).trans ready.native.2.1,
      (idx 2 s (by decide) (by decide) (by decide)).trans ready.native.2.2.1,
      (idx 3 s (by decide) (by decide) (by decide)).trans ready.native.2.2.2⟩
    base := (idx 17 s (by decide) (by decide) (by decide)).trans ready.base
    componentIndex := fields.2
    denominator := (norm_store_component_denominator guarded ops input row tid iteration component s).trans ready.denominator
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block)
      (norm_store_component_epochs guarded ops input row tid iteration component s)).trans ready.epoch
    future := norm_store_component_future guarded ops input row tid iteration component s hc ready.future
    present := norm_store_component_present guarded ops input row tid iteration component s ready.present
    buffered := norm_store_component_buffered guarded ops input row tid iteration component 8 s ready.buffered }

theorem norm_store_component_outputs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (outputs : NormOutputs ops input row tid iteration component s) :
    NormOutputs ops input row tid iteration (component+1) (normStoreAfter guarded ops input row tid iteration component s) := by
  intro c hc hcol
  by_cases he : c=component
  · subst c
    rewrite [norm_store_component_memory,if_pos hcol,if_pos rfl]
    rfl
  · rewrite [norm_store_component_memory_other guarded ops input row tid iteration component s _ (by
      intro heq
      have ho := congrArg Location.offset heq
      change address row (column tid iteration c)=address row (column tid iteration component) at ho
      unfold address column at ho
      omega)]
    exact outputs c (by omega) hcol

theorem norm_store_component_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) :
    (normStoreAfter guarded ops input row tid iteration component s).trace.length=
      s.trace.length+if column tid iteration component<50257 then 2 else 0 := by
  rewrite [norm_store_component_trace]
  split <;> simp

#print axioms norm_store_component_memory_other
#print axioms norm_store_component_buffered
#print axioms norm_store_component_present
#print axioms norm_store_component_future
#print axioms norm_store_component_ready
#print axioms norm_store_component_outputs
#print axioms norm_store_component_trace_length
end LarkNativeSoftmax
