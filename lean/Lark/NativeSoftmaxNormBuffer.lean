import Lark.NativeSoftmaxNormLoadLoop

/-! Actual outer test, eight component buffer loads, false inner-loop exit and
store-loop initialization. Both programs reach their own store-loop PC with
all valid converted inputs retained and without changing any global cell. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure NormStoreReady (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) : Prop where
  valid : row<p.rows
  bound : tid<1024
  pc : s.pc (row*1024+tid)=normPc guarded 105
  native : MaxNativeIndices (row*1024+tid) s
  base : s.indices (row*1024+tid) 17=some ((base tid iteration : Nat) : Int)
  componentIndex : s.indices (row*1024+tid) 21=some (component : Int)
  denominator : s.regs (row*1024+tid) 12=some (rowExpSum ops input row)
  epoch : (s.epochs (row*1024+tid)).block=4
  future : NormFuture ops input row tid (iteration+1) s
  present : NormPresent row s
  buffered : NormBuffered ops input row tid iteration 8 s

def normLoadBegin (t : Nat) (s : State α) : State α := setIndex (advance s t 96) t 18 0 97

theorem norm_load_begin_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α) (ht : tid<1024) (hi : iteration<7)
    (hp : s.pc t=95) (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normLoadBegin t s) := by
  have hb : base tid iteration<50257 := by unfold base; omega
  have pred := predicate_lt_of (geometry p) t s (.ivar 17) (.const 50257)
    (base tid iteration : Int) 50257 h17 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 17) (.const 50257)) (normPc guarded 115)) s=
      some (advance s t 96) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 18 97 (.const 0) (advance s t 96) 0 rfl (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 95 _ _ s _ (norm_outer_codes guarded).1 hp e1]
  exact scalar_step p guarded ops t 96 extra _ _ _ (norm_outer_codes guarded).2.1 (by simp [advance]) e2

theorem norm_load_begin_fields (t : Nat) (s : State α) :
    (normLoadBegin t s).pc t=97 ∧ (normLoadBegin t s).indices t 18=some 0 ∧
    (normLoadBegin t s).memory=s.memory ∧ (normLoadBegin t s).epochs=s.epochs ∧
    (normLoadBegin t s).regs=s.regs ∧ (normLoadBegin t s).trace=s.trace := by
  simp [normLoadBegin,setIndex,advance]

theorem norm_load_begin_index_other (t r : Nat) (s : State α) (hr : r ≠ 18) :
    (normLoadBegin t s).indices t r=s.indices t r := by simp [normLoadBegin,setIndex,advance,hr]

theorem norm_load_begin_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (ready : NormRoundReady p ops input row tid iteration s) :
    NormLoadReady p ops input row tid iteration 0 (normLoadBegin (row*1024+tid) s) := by
  obtain ⟨hp,h18,hm,he,hr,_⟩ := norm_load_begin_fields (row*1024+tid) s
  exact {
    valid := ready.valid
    bound := ready.bound
    pc := hp
    native := by simpa only [MaxNativeIndices,normLoadBegin,setIndex,advance,↓reduceIte] using ready.native
    base := (norm_load_begin_index_other (row*1024+tid) 17 s (by decide)).trans ready.base
    componentIndex := h18
    denominator := (congrArg (fun regs => regs (row*1024+tid) 12) hr).trans ready.denominator
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block) he).trans ready.epoch
    future := norm_future_memory ops input row tid iteration s _ hm ready.future
    present := norm_present_memory row s _ hm ready.present }

def normLoadFinish (guarded : Bool) (t : Nat) (s : State α) : State α :=
  setIndex (advance s t (normPc guarded 104)) t 21 0 (normPc guarded 105)

theorem norm_load_finish_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t extra : Nat) (s : State α) (hp : s.pc t=97) (h18 : s.indices t 18=some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normLoadFinish guarded t s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 18) (.const 8) 8 8 h18 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 18) (.const 8)) (normPc guarded 104)) s=
      some (advance s t (normPc guarded 104)) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 21 (normPc guarded 105) (.const 0)
    (advance s t (normPc guarded 104)) 0 rfl (by simp only [advance,↓reduceIte]; exact (norm_pc_next guarded 104).symm)
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 97 _ _ s _ (norm_outer_codes guarded).2.2 hp e1]
  exact scalar_step p guarded ops t (normPc guarded 104) extra _ _ _ (norm_store_init_code guarded)
    (by simp [advance]) e2

theorem norm_load_finish_fields (guarded : Bool) (t : Nat) (s : State α) :
    (normLoadFinish guarded t s).pc t=normPc guarded 105 ∧
    (normLoadFinish guarded t s).indices t 21=some 0 ∧
    (normLoadFinish guarded t s).memory=s.memory ∧ (normLoadFinish guarded t s).epochs=s.epochs ∧
    (normLoadFinish guarded t s).regs=s.regs ∧ (normLoadFinish guarded t s).trace=s.trace := by
  simp [normLoadFinish,setIndex,advance]

theorem norm_load_finish_index_other (guarded : Bool) (t r : Nat) (s : State α) (hr : r ≠ 21) :
    (normLoadFinish guarded t s).indices t r=s.indices t r := by simp [normLoadFinish,setIndex,advance,hr]

theorem norm_load_finish_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (ready : NormLoadReady p ops input row tid iteration 8 s)
    (buffered : NormBuffered ops input row tid iteration 8 s) :
    NormStoreReady p guarded ops input row tid iteration 0 (normLoadFinish guarded (row*1024+tid) s) := by
  obtain ⟨hp,h21,hm,he,hr,_⟩ := norm_load_finish_fields guarded (row*1024+tid) s
  exact {
    valid := ready.valid
    bound := ready.bound
    pc := hp
    native := by simpa only [MaxNativeIndices,normLoadFinish,setIndex,advance,↓reduceIte] using ready.native
    base := (norm_load_finish_index_other guarded (row*1024+tid) 17 s (by decide)).trans ready.base
    componentIndex := h21
    denominator := (congrArg (fun regs => regs (row*1024+tid) 12) hr).trans ready.denominator
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block) he).trans ready.epoch
    future := by
      intro it hi hib c hc hcol
      rewrite [hm]
      exact ready.future it (by omega) hib c hc hcol
    present := norm_present_memory row s _ hm ready.present
    buffered := by intro c hc hcol; rewrite [hm]; exact buffered c hc hcol }

def normBufferState (guarded : Bool) (ops : Ops α) (row tid iteration : Nat) (s : State α) : State α :=
  normLoadFinish guarded (row*1024+tid)
    (normLoads guarded ops row tid iteration 0 8 (normLoadBegin (row*1024+tid) s))

def normBufferCost (guarded : Bool) (tid iteration : Nat) : Nat := 2+normLoadsCost guarded tid iteration 0 8+2

theorem norm_buffer_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (hi : iteration<7)
    (ready : NormRoundReady p ops input row tid iteration s) :
    NormStoreReady p guarded ops input row tid iteration 0 (normBufferState guarded ops row tid iteration s) := by
  have started := norm_load_begin_ready p ops input row tid iteration s ready
  have loaded := norm_loads_ready p guarded ops input row tid iteration 0 8 _ started
  have buffered := norm_loads_buffered guarded ops input row tid iteration 0 8 _ hi (by decide) started.future
    (norm_buffered_empty ops input row tid iteration _)
  exact norm_load_finish_ready p guarded ops input row tid iteration _ loaded buffered

theorem norm_buffer_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration extra : Nat) (s : State α) (hi : iteration<7)
    (ready : NormRoundReady p ops input row tid iteration s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid)
      (extra+normBufferCost guarded tid iteration) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normBufferState guarded ops row tid iteration s) := by
  have started := norm_load_begin_ready p ops input row tid iteration s ready
  have loaded := norm_loads_ready p guarded ops input row tid iteration 0 8 _ started
  rewrite [show extra+normBufferCost guarded tid iteration=((extra+2)+normLoadsCost guarded tid iteration 0 8)+2 by
    unfold normBufferCost; omega,
    norm_load_begin_eq p guarded ops (row*1024+tid) tid iteration _ s ready.bound hi ready.pc ready.base,
    norm_loads_eq p guarded ops input row tid iteration 0 8 (extra+2) _ hi (by decide) started]
  exact norm_load_finish_eq p guarded ops (row*1024+tid) extra _ loaded.pc loaded.componentIndex

theorem norm_buffer_cost_bound (guarded : Bool) (tid iteration : Nat) : normBufferCost guarded tid iteration≤68 := by
  have h := norm_loads_cost_bound guarded tid iteration 0 8
  unfold normBufferCost
  omega

#print axioms norm_load_begin_eq
#print axioms norm_load_begin_fields
#print axioms norm_load_begin_index_other
#print axioms norm_load_begin_ready
#print axioms norm_load_finish_eq
#print axioms norm_load_finish_fields
#print axioms norm_load_finish_index_other
#print axioms norm_load_finish_ready
#print axioms norm_buffer_ready
#print axioms norm_buffer_eq
#print axioms norm_buffer_cost_bound
end LarkNativeSoftmax
