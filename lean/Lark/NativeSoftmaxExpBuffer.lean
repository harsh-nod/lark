import Lark.NativeSoftmaxExpLoadLoop

/-! Source boundaries around the eight-element input-buffer loop. The actual
outer-loop test and initialization, false inner exit and store-loop initializer
lead to PC57. No exponential output has yet been computed by this milestone. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure ExpRoundReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (offset acc : α) (s : State α) : Prop where
  pc : s.pc t=46
  thread : t=row*1024+tid
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  baseIndex : s.indices t 9=some ((base tid iteration : Nat) : Int)
  maximum : s.regs t 5=some offset
  accumulator : s.regs t 6=some acc
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

structure ExpStoreReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (offset acc : α) (s : State α) : Prop where
  pc : s.pc t=57
  thread : t=row*1024+tid
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  baseIndex : s.indices t 9=some ((base tid iteration : Nat) : Int)
  componentIndex : s.indices t 13=some (component : Int)
  maximum : s.regs t 5=some offset
  accumulator : s.regs t 6=some acc
  buffered : ExpBuffered ops input row tid iteration t 8 s
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

theorem exp_round_ready_of_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (offset : α) (row tid t : Nat) (s : State α) (hthread : t=row*1024+tid)
    (entry : ExpEntry p ops input offset row tid t s) :
    ExpRoundReady p input row tid 0 t offset (ops.literal 0 1) s :=
  ⟨entry.pc,hthread,entry.rowIndex,entry.tidIndex,entry.baseIndex,entry.maximum,entry.accumulator,entry.reads,entry.good⟩

def expLoadBegin (t : Nat) (s : State α) : State α := setIndex (advance s t 47) t 10 0 48

theorem exp_load_begin_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α) (ht : tid<1024) (hi : iteration<7)
    (hp : s.pc t=46) (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expLoadBegin t s) := by
  have hb : base tid iteration<50257 := by unfold base; omega
  have pred := predicate_lt_of (geometry p) t s (.ivar 9) (.const 50257)
    (base tid iteration : Int) 50257 h9 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 9) (.const 50257)) 69) s=
      some (advance s t 47) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 10 48 (.const 0) (advance s t 47) 0 rfl
    (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 46 _ _ s _ (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 47 extra _ _ _ (by cases guarded <;> rfl) (by simp [advance]) e2

theorem exp_load_begin_fields (t : Nat) (s : State α) :
    (expLoadBegin t s).pc t=48 ∧ (expLoadBegin t s).indices t 10=some 0 ∧
    (expLoadBegin t s).memory=s.memory ∧ (expLoadBegin t s).epochs=s.epochs ∧
    (expLoadBegin t s).regs=s.regs ∧ (expLoadBegin t s).trace=s.trace := by
  simp [expLoadBegin,setIndex,advance]

theorem exp_load_begin_index_other (t r : Nat) (s : State α) (hr : r ≠ 10) :
    (expLoadBegin t s).indices t r=s.indices t r := by simp [expLoadBegin,setIndex,advance,hr]

theorem exp_load_begin_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (offset acc : α) (s : State α)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    ExpLoadReady p input row tid iteration 0 t offset acc (expLoadBegin t s) := by
  obtain ⟨hp,h10,hm,_,hreg,htrace⟩ := exp_load_begin_fields t s
  exact {
    pc := hp
    rowIndex := (exp_load_begin_index_other t 0 s (by decide)).trans ready.rowIndex
    tidIndex := (exp_load_begin_index_other t 1 s (by decide)).trans ready.tidIndex
    baseIndex := (exp_load_begin_index_other t 9 s (by decide)).trans ready.baseIndex
    componentIndex := h10
    maximum := (congrArg (fun regs => regs t 5) hreg).trans ready.maximum
    accumulator := (congrArg (fun regs => regs t 6) hreg).trans ready.accumulator
    reads := by intro i hb; rewrite [hm]; exact ready.reads i hb
    good := by rewrite [htrace]; exact ready.good }

def expLoadFinish (t : Nat) (s : State α) : State α := setIndex (advance s t 56) t 13 0 57

theorem exp_load_finish_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t extra : Nat) (s : State α) (hp : s.pc t=48) (h10 : s.indices t 10=some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expLoadFinish t s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 10) (.const 8) 8 8 h10 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 8)) 56) s=
      some (advance s t 56) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 13 57 (.const 0) (advance s t 56) 0 rfl
    (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 48 _ _ s _ (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 56 extra _ _ _ (by cases guarded <;> rfl) (by simp [advance]) e2

theorem exp_load_finish_fields (t : Nat) (s : State α) :
    (expLoadFinish t s).pc t=57 ∧ (expLoadFinish t s).indices t 13=some 0 ∧
    (expLoadFinish t s).memory=s.memory ∧ (expLoadFinish t s).epochs=s.epochs ∧
    (expLoadFinish t s).regs=s.regs ∧ (expLoadFinish t s).trace=s.trace := by
  simp [expLoadFinish,setIndex,advance]

theorem exp_load_finish_index_other (t r : Nat) (s : State α) (hr : r ≠ 13) :
    (expLoadFinish t s).indices t r=s.indices t r := by simp [expLoadFinish,setIndex,advance,hr]

theorem exp_load_finish_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (offset acc : α) (s : State α) (hthread : t=row*1024+tid)
    (ready : ExpLoadReady p input row tid iteration 8 t offset acc s)
    (buffered : ExpBuffered ops input row tid iteration t 8 s) :
    ExpStoreReady p ops input row tid iteration 0 t offset acc (expLoadFinish t s) := by
  obtain ⟨hp,h13,hm,_,hreg,htrace⟩ := exp_load_finish_fields t s
  exact {
    pc := hp
    thread := hthread
    rowIndex := (exp_load_finish_index_other t 0 s (by decide)).trans ready.rowIndex
    tidIndex := (exp_load_finish_index_other t 1 s (by decide)).trans ready.tidIndex
    baseIndex := (exp_load_finish_index_other t 9 s (by decide)).trans ready.baseIndex
    componentIndex := h13
    maximum := (congrArg (fun regs => regs t 5) hreg).trans ready.maximum
    accumulator := (congrArg (fun regs => regs t 6) hreg).trans ready.accumulator
    buffered := by intro i hi; rewrite [hm]; exact buffered i hi
    reads := by intro i hi; rewrite [hm]; exact ready.reads i hi
    good := by rewrite [htrace]; exact ready.good }

def expBufferState (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) : State α :=
  expLoadFinish t (expLoads ops input row tid iteration t 0 8 (expLoadBegin t s))

def expBufferCost (tid iteration : Nat) : Nat := 2+expLoadsCost tid iteration 0 8+2

theorem exp_buffer_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (offset acc : α) (s : State α)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    ExpStoreReady p ops input row tid iteration 0 t offset acc (expBufferState ops input row tid iteration t s) := by
  have started := exp_load_begin_ready p input row tid iteration t offset acc s ready
  have loaded := exp_loads_ready p ops input row tid iteration t 0 8 offset acc _ started
  have buffered := exp_loads_buffered ops input row tid iteration t 0 8 (expLoadBegin t s)
    (by intro i hi; omega)
  exact exp_load_finish_ready p ops input row tid iteration t offset acc _ ready.thread loaded buffered

theorem exp_buffer_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (offset acc : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+expBufferCost tid iteration) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expBufferState ops input row tid iteration t s) := by
  have started := exp_load_begin_ready p input row tid iteration t offset acc s ready
  have loaded := exp_loads_ready p ops input row tid iteration t 0 8 offset acc _ started
  rewrite [show extra+expBufferCost tid iteration=((extra+2)+expLoadsCost tid iteration 0 8)+2 by
    unfold expBufferCost; omega]
  rewrite [exp_load_begin_eq p guarded ops t tid iteration _ s ht hi ready.pc ready.baseIndex]
  rewrite [exp_loads_eq p guarded ops input row tid iteration t 0 8 (extra+2) offset acc _ hr ht hi (by decide) started]
  exact exp_load_finish_eq p guarded ops t extra _ loaded.pc loaded.componentIndex

theorem exp_buffer_cost_bound (tid iteration : Nat) : expBufferCost tid iteration≤68 := by
  have h := exp_loads_cost_bound tid iteration 0 8
  unfold expBufferCost
  omega

theorem exp_buffer_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (expBufferState ops input row tid iteration t s).trace.length=s.trace.length+16 := by
  have h := exp_loads_trace_length ops input row tid iteration t 0 8 (expLoadBegin t s)
  change (expLoadFinish t _).trace.length=_
  rewrite [(exp_load_finish_fields t _).2.2.2.2.2,h,(exp_load_begin_fields t s).2.2.2.2.2]
  rfl

theorem exp_buffer_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) (l : Location)
    (hl : l.space ≠ .local ∨ l.owner ≠ t ∨ l.buffer ≠ 0) :
    (expBufferState ops input row tid iteration t s).memory l=s.memory l := by
  have h := exp_loads_memory_other ops input row tid iteration t 0 8 (expLoadBegin t s) l hl
  exact h

theorem exp_maximum_buffer_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid extra : Nat) (s : State α) (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
        (extra+3+expBufferCost tid 0) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (expBufferState ops input row tid 0 (row*1024+tid)
          (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s)) := by
  have started := exp_start_maximum_ready p ops input row tid s ready ht
  have entry := exp_round_ready_of_entry p ops input _ row tid (row*1024+tid) _ rfl started
  rewrite [show extra+3+expBufferCost tid 0=(extra+expBufferCost tid 0)+3 by omega,
    exp_start_maximum_eq p guarded ops input row tid _ s ready ht]
  exact exp_buffer_eq p guarded ops input row tid 0 (row*1024+tid) extra _ _ _ ready.valid ht (by decide) entry

theorem exp_first_buffer_cost (tid : Nat) (ht : tid<1024) : expBufferCost tid 0=60 := by
  have hc : ∀ component, component<8 → expLoadCost tid 0 component=7 := by
    intro component hcomp
    have hcol : column tid 0 component<50257 := by unfold column; omega
    simp only [expLoadCost,clampCost,if_neg (show ¬50257≤column tid 0 component by omega)]
  simp only [expBufferCost,expLoadsCost,hc 0 (by decide),hc 1 (by decide),hc 2 (by decide),
    hc 3 (by decide),hc 4 (by decide),hc 5 (by decide),hc 6 (by decide),hc 7 (by decide)]

theorem exp_maximum_buffer_native_fuel (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : MaximumReady p ops input row s) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) 4033
        (expBufferState ops input row tid 0 (row*1024+tid)
          (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s)) := by
  have h := exp_maximum_buffer_eq p guarded ops input row tid 4033 s ready ht
  rewrite [exp_first_buffer_cost tid ht] at h
  exact h

def firstExpBufferState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) : State α :=
  expBufferState ops input row tid 0 (row*1024+tid)
    (expStart ops (rowMaximum ops input row) (row*1024+tid) tid (maximumState p ops input row s))

theorem initial_exp_buffer_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ExpStoreReady p ops input row tid 0 0 (row*1024+tid) (rowMaximum ops input row) (ops.literal 0 1)
      (firstExpBufferState p ops input row tid (initial (layout p) input outside)) := by
  have maximum := initial_maximum_ready p ops input outside row hr
  have started := exp_start_maximum_ready p ops input row tid _ maximum ht
  exact exp_buffer_ready p ops input row tid 0 (row*1024+tid) _ _ _
    (exp_round_ready_of_entry p ops input _ row tid (row*1024+tid) _ rfl started)

theorem initial_exp_buffer_native_fuel (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) fuel.lane
        (maximumState p ops input row (initial (layout p) input outside)) =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) 4033
        (firstExpBufferState p ops input row tid (initial (layout p) input outside)) :=
  exp_maximum_buffer_native_fuel p guarded ops input row tid _ (initial_maximum_ready p ops input outside row hr) ht

#print axioms exp_round_ready_of_entry
#print axioms exp_load_begin_eq
#print axioms exp_load_begin_fields
#print axioms exp_load_begin_index_other
#print axioms exp_load_begin_ready
#print axioms exp_load_finish_eq
#print axioms exp_load_finish_fields
#print axioms exp_load_finish_index_other
#print axioms exp_load_finish_ready
#print axioms exp_buffer_ready
#print axioms exp_buffer_eq
#print axioms exp_buffer_cost_bound
#print axioms exp_buffer_trace_length
#print axioms exp_buffer_memory_other
#print axioms exp_maximum_buffer_eq
#print axioms exp_first_buffer_cost
#print axioms exp_maximum_buffer_native_fuel
#print axioms initial_exp_buffer_ready
#print axioms initial_exp_buffer_native_fuel
end LarkNativeSoftmax
