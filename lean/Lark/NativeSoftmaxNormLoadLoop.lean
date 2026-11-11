import Lark.NativeSoftmaxNormLoadReady

/-! Induction over the actual normalization input loop of either bound source.
Every valid private slot receives the converted exponential output, with exact
instruction fuel and access counts. No output normalization has occurred here. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normLoads (guarded : Bool) (ops : Ops α) (row tid iteration : Nat) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | component,count+1,s => normLoads guarded ops row tid iteration (component+1) count
      (normLoadState guarded ops row tid iteration component (row*1024+tid) s)

def normLoadsCost (guarded : Bool) (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => normLoadCost guarded (column tid iteration component)+
      normLoadsCost guarded tid iteration (component+1) count

def normLoadsCount (guarded : Bool) (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => (if guarded=false ∨ column tid iteration component<50257 then 1 else 0)+
      normLoadsCount guarded tid iteration (component+1) count

theorem norm_loads_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α)
    (ready : NormLoadReady p ops input row tid iteration component s) :
    NormLoadReady p ops input row tid iteration (component+count)
      (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => simpa only [normLoads,Nat.add_zero] using ready
  | succ count ih =>
    have tail := ih (component+1) _ (norm_load_component_ready p guarded ops input row tid iteration component s ready)
    simpa only [normLoads,show component+1+count=component+(count+1) by omega] using tail

theorem norm_loads_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count extra : Nat) (s : State α) (hi : iteration<7)
    (hc : component+count≤8) (ready : NormLoadReady p ops input row tid iteration component s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
      (extra+normLoadsCost guarded tid iteration component count) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    have head := norm_load_component_ready p guarded ops input row tid iteration component s ready
    have ht := ready.bound
    have hrow : (row*1024+tid)/1024=row := by omega
    have h0 : s.indices (row*1024+tid) 0=some (row : Int) := by
      simpa only [hrow] using ready.native.1
    simp only [normLoadsCost,normLoads]
    rewrite [show extra+(normLoadCost guarded (column tid iteration component)+normLoadsCost guarded tid iteration (component+1) count)=
      (extra+normLoadsCost guarded tid iteration (component+1) count)+normLoadCost guarded (column tid iteration component) by omega]
    rewrite [norm_load_component_eq p guarded ops row tid iteration component (row*1024+tid) _ s
      ready.valid ready.bound hi (by omega) h0 ready.base ready.componentIndex ready.pc ready.present]
    exact ih (component+1) _ (by omega) head

theorem norm_loads_future (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count start : Nat) (s : State α) (hf : NormFuture ops input row tid start s) :
    NormFuture ops input row tid start (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => exact hf
  | succ count ih =>
    exact ih (component+1) _
      (norm_load_component_future guarded ops input row tid iteration component (row*1024+tid) start s hf)

theorem norm_loads_buffered (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component count : Nat) (s : State α) (hi : iteration<7) (hc : component+count≤8)
    (future : NormFuture ops input row tid iteration s)
    (buffered : NormBuffered ops input row tid iteration component s) :
    NormBuffered ops input row tid iteration (component+count)
      (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => simpa only [normLoads,Nat.add_zero] using buffered
  | succ count ih =>
    have head := norm_load_component_buffered guarded ops input row tid iteration component s hi (by omega) future buffered
    have hf := norm_load_component_future guarded ops input row tid iteration component (row*1024+tid) iteration s future
    have tail := ih (component+1) _ (by omega) hf head
    simpa only [normLoads,show component+1+count=component+(count+1) by omega] using tail

theorem norm_loads_epochs (guarded : Bool) (ops : Ops α)
    (row tid iteration component count : Nat) (s : State α) :
    (normLoads guarded ops row tid iteration component count s).epochs=s.epochs := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (norm_load_component_epochs guarded ops row tid iteration component (row*1024+tid) s)

theorem norm_loads_regs (guarded : Bool) (ops : Ops α)
    (row tid iteration component count : Nat) (s : State α) :
    (normLoads guarded ops row tid iteration component count s).regs=s.regs := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (norm_load_component_regs guarded ops row tid iteration component (row*1024+tid) s)

theorem norm_loads_index_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component count r : Nat) (s : State α) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) :
    (normLoads guarded ops row tid iteration component count s).indices (row*1024+tid) r=s.indices (row*1024+tid) r := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (norm_load_component_index_other guarded ops row tid iteration component (row*1024+tid) r s h18 h19 h20)

theorem norm_loads_memory_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component count : Nat) (s : State α) (l : Location)
    (hl : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 1) :
    (normLoads guarded ops row tid iteration component count s).memory l=s.memory l := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    apply (ih (component+1) _).trans
    apply norm_load_component_memory_other guarded ops row tid iteration component (row*1024+tid) s l
    intro he
    rcases hl with hs | ho | hb
    · exact hs (congrArg Location.space he)
    · exact ho (congrArg Location.owner he)
    · exact hb (congrArg Location.buffer he)

theorem norm_loads_trace_length (guarded : Bool) (ops : Ops α)
    (row tid iteration component count : Nat) (s : State α) :
    (normLoads guarded ops row tid iteration component count s).trace.length=
      s.trace.length+2*normLoadsCount guarded tid iteration component count := by
  induction count generalizing component s with
  | zero => simp [normLoads,normLoadsCount]
  | succ count ih =>
    change (normLoads guarded ops row tid iteration (component+1) count _).trace.length=_
    rewrite [ih,norm_load_component_trace_length]
    simp only [normLoadsCount]
    split <;> omega

theorem norm_loads_fixed_good (ops : Ops α) (row tid iteration component count : Nat)
    (s : State α) (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normLoads true ops row tid iteration component count s).trace, Good a := by
  induction count generalizing component s with
  | zero => exact good
  | succ count ih => exact ih (component+1) _ (norm_load_component_fixed_good ops row tid iteration component s ht good)

theorem norm_load_cost_bounds (guarded : Bool) (col : Nat) :
    5≤normLoadCost guarded col ∧ normLoadCost guarded col≤8 := by
  cases guarded <;> unfold normLoadCost normChoiceCost clampCost <;>
    by_cases hc : col<50257 <;> simp [hc,show (50257≤col) ↔ ¬ col<50257 by omega]

theorem norm_loads_cost_bound (guarded : Bool) (tid iteration component count : Nat) :
    normLoadsCost guarded tid iteration component count≤8*count := by
  induction count generalizing component with
  | zero => simp [normLoadsCost]
  | succ count ih =>
    have h := (norm_load_cost_bounds guarded (column tid iteration component)).2
    have tail := ih (component+1)
    simp only [normLoadsCost]
    omega

#print axioms norm_loads_ready
#print axioms norm_loads_eq
#print axioms norm_loads_future
#print axioms norm_loads_buffered
#print axioms norm_loads_epochs
#print axioms norm_loads_regs
#print axioms norm_loads_index_other
#print axioms norm_loads_memory_other
#print axioms norm_loads_trace_length
#print axioms norm_loads_fixed_good
#print axioms norm_load_cost_bounds
#print axioms norm_loads_cost_bound
end LarkNativeSoftmax
