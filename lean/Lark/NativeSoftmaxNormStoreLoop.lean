import Lark.NativeSoftmaxNormStoreReady

/-! Induction over the normalization output loop. Each valid component stores
the converted division result, retaining earlier outputs and future-round
inputs. The actual false exit and outer-loop increment remain separate. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStores (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row tid iteration : Nat) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | component,count+1,s => normStores guarded ops input row tid iteration (component+1) count
      (normStoreAfter guarded ops input row tid iteration component s)

def normStoresCost (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => normStoreCost tid iteration component+normStoresCost tid iteration (component+1) count

def normStoresCount (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => (if column tid iteration component<50257 then 1 else 0)+normStoresCount tid iteration (component+1) count

theorem norm_stores_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) (hc : component+count≤8)
    (ready : NormStoreReady p guarded ops input row tid iteration component s) :
    NormStoreReady p guarded ops input row tid iteration (component+count)
      (normStores guarded ops input row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => simpa only [normStores,Nat.add_zero] using ready
  | succ count ih =>
    have head := norm_store_component_ready p guarded ops input row tid iteration component s (by omega) ready
    have tail := ih (component+1) _ (by omega) head
    simpa only [normStores,show component+1+count=component+(count+1) by omega] using tail

theorem norm_stores_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count extra : Nat) (s : State α) (hi : iteration<7) (hc : component+count≤8)
    (ready : NormStoreReady p guarded ops input row tid iteration component s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
      (extra+normStoresCost tid iteration component count) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normStores guarded ops input row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    have head := norm_store_component_ready p guarded ops input row tid iteration component s (by omega) ready
    simp only [normStoresCost,normStores]
    rewrite [show extra+(normStoreCost tid iteration component+normStoresCost tid iteration (component+1) count)=
      (extra+normStoresCost tid iteration (component+1) count)+normStoreCost tid iteration component by omega,
      norm_store_component_eq p guarded ops input row tid iteration component _ s hi (by omega) ready]
    exact ih (component+1) _ (by omega) head

theorem norm_stores_outputs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) (outputs : NormOutputs ops input row tid iteration component s) :
    NormOutputs ops input row tid iteration (component+count) (normStores guarded ops input row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => simpa only [normStores,Nat.add_zero] using outputs
  | succ count ih =>
    have tail := ih (component+1) _ (norm_store_component_outputs guarded ops input row tid iteration component s outputs)
    simpa only [normStores,show component+1+count=component+(count+1) by omega] using tail

theorem norm_stores_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) :
    (normStores guarded ops input row tid iteration component count s).epochs=s.epochs := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans (norm_store_component_epochs guarded ops input row tid iteration component s)

theorem norm_stores_denominator (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) :
    (normStores guarded ops input row tid iteration component count s).regs (row*1024+tid) 12=s.regs (row*1024+tid) 12 := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans (norm_store_component_denominator guarded ops input row tid iteration component s)

theorem norm_stores_index_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count r : Nat) (s : State α) (h21 : r ≠ 21) (h22 : r ≠ 22) (h23 : r ≠ 23) :
    (normStores guarded ops input row tid iteration component count s).indices (row*1024+tid) r=s.indices (row*1024+tid) r := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans (norm_store_component_index_other guarded ops input row tid iteration component r s h21 h22 h23)

theorem norm_stores_memory_frame (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) (l : Location)
    (hl : ∀ c, component≤c → c<component+count → column tid iteration c<50257 →
      l ≠ globalCell 0 (address row (column tid iteration c))) :
    (normStores guarded ops input row tid iteration component count s).memory l=s.memory l := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    apply (ih (component+1) _ (by intro c hlo hhi hcol; exact hl c (by omega) (by omega) hcol)).trans
    rewrite [norm_store_component_memory]
    by_cases hc : column tid iteration component<50257
    · simp only [if_pos hc,if_neg (hl component (by omega) (by omega) hc)]
    · simp only [if_neg hc]

theorem norm_stores_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) :
    (normStores guarded ops input row tid iteration component count s).trace.length=
      s.trace.length+2*normStoresCount tid iteration component count := by
  induction count generalizing component s with
  | zero => simp [normStores,normStoresCount]
  | succ count ih =>
    change (normStores guarded ops input row tid iteration (component+1) count _).trace.length=_
    rewrite [ih,norm_store_component_trace_length]
    simp only [normStoresCount]
    split <;> omega

theorem norm_stores_good (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normStores guarded ops input row tid iteration component count s).trace, Good a := by
  induction count generalizing component s with
  | zero => exact good
  | succ count ih =>
    exact ih (component+1) _ (norm_store_component_good guarded ops input row tid iteration component s ht good)

theorem norm_store_component_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normStoreAfter guarded ops input row tid iteration component s) := by
  have hh := norm_store_head_other guarded tid iteration component (row*1024+tid) u s hu
  have hm : OtherThread (row*1024+tid) u s (normStoreMiddle guarded ops input row tid iteration component s) := by
    by_cases hc : column tid iteration component<50257
    · simp only [normStoreMiddle,if_pos hc]
      exact other_thread_trans (row*1024+tid) u _ _ _ hh
        (norm_store_body_other guarded ops _ _ row _ component (row*1024+tid) u _ hu)
    · simpa only [normStoreMiddle,if_neg hc] using hh
  exact other_thread_trans (row*1024+tid) u _ _ _ hm (norm_store_next_other guarded (row*1024+tid) component u _ hu)

theorem norm_stores_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normStores guarded ops input row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans (row*1024+tid) u _ _ _ (norm_store_component_other guarded ops input row tid iteration component u s hu)
      (ih (component+1) _)

theorem norm_stores_cost_bound (tid iteration component count : Nat) : normStoresCost tid iteration component count≤8*count := by
  induction count generalizing component with
  | zero => simp [normStoresCost]
  | succ count ih =>
    have h : normStoreCost tid iteration component≤8 := by unfold normStoreCost; split <;> decide
    have tail := ih (component+1)
    simp only [normStoresCost]
    omega

#print axioms norm_stores_ready
#print axioms norm_stores_eq
#print axioms norm_stores_outputs
#print axioms norm_stores_epochs
#print axioms norm_stores_denominator
#print axioms norm_stores_index_other
#print axioms norm_stores_memory_frame
#print axioms norm_stores_trace_length
#print axioms norm_stores_good
#print axioms norm_store_component_other
#print axioms norm_stores_other
#print axioms norm_stores_cost_bound
end LarkNativeSoftmax
