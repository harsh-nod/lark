import Lark.NativeSoftmaxNormLoad

/-! Value, memory, native-index and trace frames of a complete normalization
buffer component. Global memory is preserved, including unused clamped cells. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_selected_column_valid (guarded : Bool) (col : Nat) (hc : col<50257) :
    normSelectedColumn guarded col=col := by
  cases guarded <;> simp [normSelectedColumn,clamped,Nat.min_eq_right (by omega : col≤50256)]

theorem norm_load_component_memory (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) (l : Location) :
    (normLoadState guarded ops row tid iteration component t s).memory l=
      if guarded=false ∨ column tid iteration component<50257 then
        if l=localCell 1 t component then
          some (ops.fromHalf (normSample ops row (normSelectedColumn guarded (column tid iteration component)) s)) else s.memory l
      else s.memory l := by
  by_cases hl : guarded=false ∨ column tid iteration component<50257 <;>
    simp [normLoadState,hl,normLoadAdvance,normLoadStored,normLoadAddress,written,record,setIndex,advance,
      (norm_load_head_frames guarded tid iteration component t s).1]

theorem norm_load_component_memory_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) (l : Location) (hl : l ≠ localCell 1 t component) :
    (normLoadState guarded ops row tid iteration component t s).memory l=s.memory l := by
  rewrite [norm_load_component_memory]
  split <;> simp [hl]

theorem norm_load_component_global (guarded : Bool) (ops : Ops α)
    (row tid iteration component t buffer offset : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).memory (globalCell buffer offset)=s.memory (globalCell buffer offset) := by
  apply norm_load_component_memory_other guarded ops row tid iteration component t s
  intro h
  have hs := congrArg Location.space h
  simp [globalCell,localCell] at hs

theorem norm_load_component_present (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) (hp : NormPresent row s) :
    NormPresent row (normLoadState guarded ops row tid iteration component t s) := by
  intro col hc
  rewrite [norm_load_component_global]
  exact hp col hc

theorem norm_load_component_future (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t start : Nat) (s : State α) (hf : NormFuture ops input row tid start s) :
    NormFuture ops input row tid start (normLoadState guarded ops row tid iteration component t s) := by
  intro it hi hib c hc hcol
  rewrite [norm_load_component_global]
  exact hf it hi hib c hc hcol

theorem norm_load_component_value (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) (hc : column tid iteration component<50257) :
    (normLoadState guarded ops row tid iteration component t s).memory (localCell 1 t component)=
      some (ops.fromHalf (normSample ops row (column tid iteration component) s)) := by
  rewrite [norm_load_component_memory,if_pos (Or.inr hc),if_pos rfl,norm_selected_column_valid guarded _ hc]
  rfl

theorem norm_sample_from_future (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hi : iteration<7) (hc : component<8)
    (hcol : column tid iteration component<50257) (hf : NormFuture ops input row tid iteration s) :
    normSample ops row (column tid iteration component) s=expOutputValue ops input row (column tid iteration component) := by
  have hm := hf iteration (Nat.le_refl _) hi component hc hcol
  simp only [normSample,hm,Option.getD_some]

theorem norm_load_component_input_value (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (hi : iteration<7) (hc : component<8)
    (hcol : column tid iteration component<50257) (hf : NormFuture ops input row tid iteration s) :
    (normLoadState guarded ops row tid iteration component t s).memory (localCell 1 t component)=
      some (ops.fromHalf (expOutputValue ops input row (column tid iteration component))) :=
  (norm_load_component_value guarded ops row tid iteration component t s hcol).trans
    (congrArg (fun value => some (ops.fromHalf value)) (norm_sample_from_future ops input row tid iteration component s hi hc hcol hf))

theorem norm_load_component_index_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component t r : Nat) (s : State α) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) :
    (normLoadState guarded ops row tid iteration component t s).indices t r=s.indices t r := by
  by_cases hl : guarded=false ∨ column tid iteration component<50257
  · simp only [normLoadState,if_pos hl,normLoadAdvance,setIndex,advance,h18,↓reduceIte,normLoadStored,written,record,normLoadAddress,h20]
    exact norm_load_head_index_other guarded tid iteration component t r s h19
  · simp only [normLoadState,if_neg hl,normLoadAdvance,setIndex,advance,h18,↓reduceIte]
    exact norm_load_head_index_other guarded tid iteration component t r s h19

theorem norm_load_component_native (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) (hi : MaxNativeIndices t s) :
    MaxNativeIndices t (normLoadState guarded ops row tid iteration component t s) := by
  exact ⟨(norm_load_component_index_other guarded ops row tid iteration component t 0 s (by decide) (by decide) (by decide)).trans hi.1,
    (norm_load_component_index_other guarded ops row tid iteration component t 1 s (by decide) (by decide) (by decide)).trans hi.2.1,
    (norm_load_component_index_other guarded ops row tid iteration component t 2 s (by decide) (by decide) (by decide)).trans hi.2.2.1,
    (norm_load_component_index_other guarded ops row tid iteration component t 3 s (by decide) (by decide) (by decide)).trans hi.2.2.2⟩

theorem norm_load_component_trace (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).trace=
      if guarded=false ∨ column tid iteration component<50257 then
        ⟨t,localCell 1 t component,true,s.epochs t⟩::
          ⟨t,globalCell 0 (address row (normSelectedColumn guarded (column tid iteration component))),false,s.epochs t⟩::s.trace
      else s.trace := by
  by_cases hl : guarded=false ∨ column tid iteration component<50257 <;>
    simp [normLoadState,hl,normLoadAdvance,normLoadStored,normLoadAddress,written,record,setIndex,advance,
      (norm_load_head_frames guarded tid iteration component t s).2.1,
      (norm_load_head_frames guarded tid iteration component t s).2.2.1]

theorem norm_load_component_trace_length (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).trace.length=
      s.trace.length+if guarded=false ∨ column tid iteration component<50257 then 2 else 0 := by
  rewrite [norm_load_component_trace]
  split <;> simp

theorem norm_load_component_good (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α)
    (hread : guarded=false ∨ column tid iteration component<50257 →
      Good ⟨t,globalCell 0 (address row (normSelectedColumn guarded (column tid iteration component))),false,s.epochs t⟩)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normLoadState guarded ops row tid iteration component t s).trace, Good a := by
  intro a ha
  rewrite [norm_load_component_trace] at ha
  by_cases hl : guarded=false ∨ column tid iteration component<50257
  · rewrite [if_pos hl] at ha
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact Good.privateAccess rfl rfl
    · rcases List.mem_cons.mp h with h | h
      · subst a; exact hread hl
      · exact good a h
  · rewrite [if_neg hl] at ha
    exact good a ha

#print axioms norm_selected_column_valid
#print axioms norm_load_component_memory
#print axioms norm_load_component_memory_other
#print axioms norm_load_component_global
#print axioms norm_load_component_present
#print axioms norm_load_component_future
#print axioms norm_load_component_value
#print axioms norm_sample_from_future
#print axioms norm_load_component_input_value
#print axioms norm_load_component_index_other
#print axioms norm_load_component_native
#print axioms norm_load_component_trace
#print axioms norm_load_component_trace_length
#print axioms norm_load_component_good
end LarkNativeSoftmax
