import Lark.NativeSoftmaxExpStoreComponent

/-! The actual eight-component exponential store loop, including source order,
valid-column counts and preservation of output cells written earlier. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expStoreFold (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid iteration : Nat) : Nat → Nat → α → α
  | _,0,acc => acc
  | component,count+1,acc => expStoreFold ops input offset row tid iteration (component+1) count
      (expStoreAcc ops input offset acc row tid iteration component)

def expStores (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid iteration t : Nat) :
    Nat → Nat → α → State α → State α
  | _,0,_,s => s
  | component,count+1,acc,s => expStores ops input offset row tid iteration t (component+1) count
      (expStoreAcc ops input offset acc row tid iteration component)
      (expStoreAfter ops input offset acc row tid iteration component t s)

def expStoresCost (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => expStoreCost tid iteration component+expStoresCost tid iteration (component+1) count

def expStoresCount (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => (if column tid iteration component<50257 then 1 else 0)+expStoresCount tid iteration (component+1) count

def ExpOutputs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration upto : Nat) (s : State α) : Prop :=
  ∀ component, component<upto → column tid iteration component<50257 →
    s.memory (globalCell 0 (address row (column tid iteration component)))=
      some (ops.toHalf (expComponentValue ops input offset row tid iteration component))

theorem exp_store_component_outputs (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t : Nat) (s : State α)
    (outputs : ExpOutputs ops input offset row tid iteration component s) :
    ExpOutputs ops input offset row tid iteration (component+1)
      (expStoreAfter ops input offset acc row tid iteration component t s) := by
  intro slot hs hcol
  by_cases he : slot=component
  · subst slot
    rewrite [exp_store_after_memory,if_pos hcol,if_pos rfl]
    rfl
  · rewrite [exp_store_after_memory_other ops input offset acc row tid iteration component t s _ (by
      intro h
      have hc := congrArg Location.offset h
      change address row (column tid iteration slot)=address row (column tid iteration component) at hc
      unfold address column at hc
      omega)]
    exact outputs slot (by omega) hcol

theorem exp_stores_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) (ht : tid<1024)
    (ready : ExpStoreReady p ops input row tid iteration component t offset acc s) :
    ExpStoreReady p ops input row tid iteration (component+count) t offset
      (expStoreFold ops input offset row tid iteration component count acc)
      (expStores ops input offset row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => simpa only [expStoreFold,expStores,Nat.add_zero] using ready
  | succ count ih =>
    have tail := ih (component+1) _ _ (exp_store_component_ready p ops input row tid iteration component t offset acc s ht ready)
    simpa only [expStoreFold,expStores,show component+1+count=component+(count+1) by omega] using tail

theorem exp_stores_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count extra : Nat) (acc : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component+count≤8)
    (ready : ExpStoreReady p ops input row tid iteration component t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra+expStoresCost tid iteration component count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStores ops input offset row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    have head := exp_store_component_ready p ops input row tid iteration component t offset acc s ht ready
    simp only [expStoresCost,expStores]
    rewrite [show extra+(expStoreCost tid iteration component+expStoresCost tid iteration (component+1) count)=
      (extra+expStoresCost tid iteration (component+1) count)+expStoreCost tid iteration component by omega]
    rewrite [exp_store_component_eq p guarded ops input row tid iteration component t _ offset acc s hr ht hi (by omega) ready]
    exact ih (component+1) _ _ (by omega) head

theorem exp_stores_outputs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α)
    (outputs : ExpOutputs ops input offset row tid iteration component s) :
    ExpOutputs ops input offset row tid iteration (component+count)
      (expStores ops input offset row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => simpa only [expStores,Nat.add_zero] using outputs
  | succ count ih =>
    have tail := ih (component+1) (expStoreAcc ops input offset acc row tid iteration component)
      (expStoreAfter ops input offset acc row tid iteration component t s)
      (exp_store_component_outputs ops input offset acc row tid iteration component t s outputs)
    simpa only [expStores,show component+1+count=component+(count+1) by omega] using tail

theorem exp_stores_trace_length (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) :
    (expStores ops input offset row tid iteration t component count acc s).trace.length=
      s.trace.length+2*expStoresCount tid iteration component count := by
  induction count generalizing component acc s with
  | zero => simp [expStores,expStoresCount]
  | succ count ih =>
    have tail := ih (component+1) (expStoreAcc ops input offset acc row tid iteration component)
      (expStoreAfter ops input offset acc row tid iteration component t s)
    change (expStores ops input offset row tid iteration t (component+1) count _ _).trace.length=_
    rewrite [tail,exp_store_after_trace_length]
    simp only [expStoresCount]
    by_cases hc : column tid iteration component<50257 <;> simp only [hc,↓reduceIte] <;> omega

theorem exp_stores_epochs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) :
    (expStores ops input offset row tid iteration t component count acc s).epochs=s.epochs := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _ _).trans (exp_store_after_epochs ops input offset acc row tid iteration component t s)

theorem exp_stores_index_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count r : Nat) (acc : α) (s : State α)
    (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expStores ops input offset row tid iteration t component count acc s).indices t r=s.indices t r := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _ _).trans (exp_store_after_index_other ops input offset acc row tid iteration component t r s h13 h14 h15)

theorem exp_stores_maximum (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) :
    (expStores ops input offset row tid iteration t component count acc s).regs t 5=s.regs t 5 := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _ _).trans (exp_store_after_maximum ops input offset acc row tid iteration component t s)

theorem exp_stores_memory_frame (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count : Nat) (acc : α) (s : State α) (l : Location)
    (hl : ∀ slot, component≤slot → slot<component+count → column tid iteration slot<50257 →
      l ≠ globalCell 0 (address row (column tid iteration slot))) :
    (expStores ops input offset row tid iteration t component count acc s).memory l=s.memory l := by
  induction count generalizing component acc s with
  | zero => rfl
  | succ count ih =>
    have tail := ih (component+1) (expStoreAcc ops input offset acc row tid iteration component)
      (expStoreAfter ops input offset acc row tid iteration component t s) (by
        intro slot hlo hhi hcol
        exact hl slot (by omega) (by omega) hcol)
    apply tail.trans
    rewrite [exp_store_after_memory]
    split
    · rename_i hc
      exact if_neg (hl component (by omega) (by omega) hc)
    · rfl

theorem exp_stores_count_bound (tid iteration component count : Nat) : expStoresCount tid iteration component count≤count := by
  induction count generalizing component with
  | zero => simp [expStoresCount]
  | succ count ih =>
    have tail := ih (component+1)
    simp only [expStoresCount]
    split <;> omega

theorem exp_stores_cost_count (tid iteration component count : Nat) :
    expStoresCost tid iteration component count=5*count+5*expStoresCount tid iteration component count := by
  induction count generalizing component with
  | zero => simp [expStoresCost,expStoresCount]
  | succ count ih =>
    have tail := ih (component+1)
    simp only [expStoresCost,expStoreCost,expStoresCount]
    by_cases hc : column tid iteration component<50257 <;> simp only [hc,↓reduceIte] <;> omega

theorem exp_stores_cost_bound (tid iteration component count : Nat) : expStoresCost tid iteration component count≤10*count := by
  have h := exp_stores_count_bound tid iteration component count
  rewrite [exp_stores_cost_count]
  omega

#print axioms exp_store_component_outputs
#print axioms exp_stores_ready
#print axioms exp_stores_eq
#print axioms exp_stores_outputs
#print axioms exp_stores_trace_length
#print axioms exp_stores_epochs
#print axioms exp_stores_index_other
#print axioms exp_stores_maximum
#print axioms exp_stores_memory_frame
#print axioms exp_stores_count_bound
#print axioms exp_stores_cost_count
#print axioms exp_stores_cost_bound
end LarkNativeSoftmax
