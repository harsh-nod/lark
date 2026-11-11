import Lark.NativeSoftmaxExpLoad

/-! Induction over the actual eight-element private input-buffer loop. Earlier
slots remain intact as subsequent components execute. The next store loop and
its exponential values are separate obligations. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expLoads (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | component,count+1,s => expLoads ops input row tid iteration t (component+1) count
      (expLoadAfter ops input row tid iteration component t s)

def expLoadsCost (tid iteration : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | component,count+1 => expLoadCost tid iteration component+expLoadsCost tid iteration (component+1) count

theorem exp_loads_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (offset acc : α) (s : State α)
    (ready : ExpLoadReady p input row tid iteration component t offset acc s) :
    ExpLoadReady p input row tid iteration (component+count) t offset acc
      (expLoads ops input row tid iteration t component count s) := by
  induction count generalizing component s with
  | zero => simpa only [expLoads,Nat.add_zero] using ready
  | succ count ih =>
    have tail := ih (component+1) _ (exp_load_ready p ops input row tid iteration component t offset acc s ready)
    simpa only [expLoads,show component+1+count=component+(count+1) by omega] using tail

theorem exp_loads_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count extra : Nat) (offset acc : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component+count≤8)
    (ready : ExpLoadReady p input row tid iteration component t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra+expLoadsCost tid iteration component count) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoads ops input row tid iteration t component count s) := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    have head := exp_load_ready p ops input row tid iteration component t offset acc s ready
    simp only [expLoadsCost,expLoads]
    rewrite [show extra+(expLoadCost tid iteration component+expLoadsCost tid iteration (component+1) count)=
      (extra+expLoadsCost tid iteration (component+1) count)+expLoadCost tid iteration component by omega]
    rewrite [exp_load_eq p guarded ops input row tid iteration component t _ s hr ht hi (by omega)
      ready.rowIndex ready.baseIndex ready.componentIndex ready.pc ready.reads]
    exact ih (component+1) _ (by omega) head

theorem exp_loads_buffered (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (s : State α)
    (buffered : ExpBuffered ops input row tid iteration t component s) :
    ExpBuffered ops input row tid iteration t (component+count)
      (expLoads ops input row tid iteration t component count s) := by
  induction count generalizing component s with
  | zero => simpa only [expLoads,Nat.add_zero] using buffered
  | succ count ih =>
    have tail := ih (component+1) _ (exp_load_buffered ops input row tid iteration component t s buffered)
    simpa only [expLoads,show component+1+count=component+(count+1) by omega] using tail

theorem exp_loads_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (s : State α) :
    (expLoads ops input row tid iteration t component count s).trace.length=s.trace.length+2*count := by
  induction count generalizing component s with
  | zero => simp [expLoads]
  | succ count ih =>
    have tail := ih (component+1) (expLoadAfter ops input row tid iteration component t s)
    change (expLoads ops input row tid iteration t (component+1) count _).trace.length=_
    rewrite [tail,(exp_load_fields ops input row tid iteration component t s).2.2.2.2]
    simp only [List.length_cons]
    omega

theorem exp_loads_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (s : State α) :
    (expLoads ops input row tid iteration t component count s).epochs=s.epochs := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (exp_load_fields ops input row tid iteration component t s).2.2.1

theorem exp_loads_regs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (s : State α) :
    (expLoads ops input row tid iteration t component count s).regs=s.regs := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (exp_load_fields ops input row tid iteration component t s).2.2.2.1

theorem exp_loads_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count r : Nat) (s : State α)
    (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) :
    (expLoads ops input row tid iteration t component count s).indices t r=s.indices t r := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    exact (ih (component+1) _).trans
      (exp_load_index_other ops input row tid iteration component t r s h10 h11 h12)

theorem exp_loads_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count : Nat) (s : State α) (l : Location)
    (hl : l.space ≠ .local ∨ l.owner ≠ t ∨ l.buffer ≠ 0) :
    (expLoads ops input row tid iteration t component count s).memory l=s.memory l := by
  induction count generalizing component s with
  | zero => rfl
  | succ count ih =>
    apply (ih (component+1) _).trans
    apply exp_load_memory_other ops input row tid iteration component t s l
    intro h
    rcases hl with hs | ho | hb
    · exact hs (congrArg Location.space h)
    · exact ho (congrArg Location.owner h)
    · exact hb (congrArg Location.buffer h)

theorem exp_load_cost_bounds (tid iteration component : Nat) :
    7≤expLoadCost tid iteration component ∧ expLoadCost tid iteration component≤8 := by
  unfold expLoadCost clampCost
  split <;> decide

theorem exp_loads_cost_bound (tid iteration component count : Nat) :
    expLoadsCost tid iteration component count≤8*count := by
  induction count generalizing component with
  | zero => simp [expLoadsCost]
  | succ count ih =>
    have head := (exp_load_cost_bounds tid iteration component).2
    have tail := ih (component+1)
    simp only [expLoadsCost]
    omega

#print axioms exp_loads_ready
#print axioms exp_loads_eq
#print axioms exp_loads_buffered
#print axioms exp_loads_trace_length
#print axioms exp_loads_epochs
#print axioms exp_loads_regs
#print axioms exp_loads_index_other
#print axioms exp_loads_memory_other
#print axioms exp_load_cost_bounds
#print axioms exp_loads_cost_bound
end LarkNativeSoftmax
