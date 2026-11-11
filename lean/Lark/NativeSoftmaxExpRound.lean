import Lark.NativeSoftmaxExpStoreLoop

/-! One complete actual exponentiation/sum outer iteration. All eight input
loads occur before any exponential stores; the source's false store-loop exit
then increments the outer index and returns to PC46. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exp_buffer_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t r : Nat) (s : State α) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (expBufferState ops input row tid iteration t s).indices t r=s.indices t r :=
  (exp_load_finish_index_other t r _ h13).trans
    ((exp_loads_index_other ops input row tid iteration t 0 8 r _ h10 h11 h12).trans
      (exp_load_begin_index_other t r s h10))

theorem exp_buffer_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (s : State α) :
    (expBufferState ops input row tid iteration t s).epochs=s.epochs :=
  (exp_load_finish_fields t _).2.2.2.1.trans
    ((exp_loads_epochs ops input row tid iteration t 0 8 _).trans (exp_load_begin_fields t s).2.2.2.1)

def expStoreFinish (t tid iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 67) t 9 ((base tid (iteration+1) : Nat) : Int) 68) t 46

theorem exp_store_finish_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α) (ht : tid<1024) (hi : iteration<7)
    (hp : s.pc t=57) (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h13 : s.indices t 13=some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expStoreFinish t tid iteration s) := by
  let s1 := advance s t 67
  let s2 := setIndex s1 t 9 ((base tid (iteration+1) : Nat) : Int) 68
  have pred := predicate_nlt_of (geometry p) t s (.ivar 13) (.const 8) 8 8 h13 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 13) (.const 8)) 67) s=some s1 := by
    simp [execute,pred,hp,s1]
  have hb : base tid iteration+8192<2147483648 := by unfold base; omega
  have ix := eval_nat_sum (geometry p) t (base tid iteration) 8192 s1 (.ivar 9) (.const 8192) h9 rfl hb
  have hbase : base tid iteration+8192=base tid (iteration+1) := by simp [base,Nat.add_mul]; omega
  have ix' : evalIndex (geometry p) t s1 (.add (.ivar 9) (.const 8192))=some ((base tid (iteration+1) : Nat) : Int) := by
    simpa only [hbase] using ix
  have e2 := execute_index_of ops (layout p) (geometry p) t 9 68 (.add (.ivar 9) (.const 8192)) s1 _ ix'
    (by simp [s1,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 46) s2=some (expStoreFinish t tid iteration s) := rfl
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 57 _ _ s s1 (by cases guarded <;> rfl) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 67 _ _ s1 s2 (by cases guarded <;> rfl) (by simp [s1,advance]) e2]
  exact scalar_step p guarded ops t 68 extra _ s2 _ (by cases guarded <;> rfl) (by simp [s2,setIndex,advance]) e3

theorem exp_store_finish_fields (t tid iteration : Nat) (s : State α) :
    (expStoreFinish t tid iteration s).pc t=46 ∧
    (expStoreFinish t tid iteration s).indices t 9=some ((base tid (iteration+1) : Nat) : Int) ∧
    (expStoreFinish t tid iteration s).memory=s.memory ∧ (expStoreFinish t tid iteration s).regs=s.regs ∧
    (expStoreFinish t tid iteration s).epochs=s.epochs ∧ (expStoreFinish t tid iteration s).trace=s.trace := by
  simp [expStoreFinish,setIndex,advance]

theorem exp_store_finish_index_other (t tid iteration r : Nat) (s : State α) (hr : r ≠ 9) :
    (expStoreFinish t tid iteration s).indices t r=s.indices t r := by simp [expStoreFinish,setIndex,advance,hr]

theorem exp_store_finish_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (offset acc : α) (s : State α)
    (ready : ExpStoreReady p ops input row tid iteration 8 t offset acc s) :
    ExpRoundReady p input row tid (iteration+1) t offset acc (expStoreFinish t tid iteration s) := by
  obtain ⟨hp,h9,hm,hreg,_,htrace⟩ := exp_store_finish_fields t tid iteration s
  exact {
    pc := hp
    thread := ready.thread
    rowIndex := (exp_store_finish_index_other t tid iteration 0 s (by decide)).trans ready.rowIndex
    tidIndex := (exp_store_finish_index_other t tid iteration 1 s (by decide)).trans ready.tidIndex
    baseIndex := h9
    maximum := (congrArg (fun regs => regs t 5) hreg).trans ready.maximum
    accumulator := (congrArg (fun regs => regs t 6) hreg).trans ready.accumulator
    reads := by intro i hb; rewrite [hm]; exact ready.reads i hb
    good := by rewrite [htrace]; exact ready.good }

def expRoundState (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : State α :=
  expStoreFinish t tid iteration
    (expStores ops input offset row tid iteration t 0 8 acc (expBufferState ops input row tid iteration t s))

def expRoundFold (ops : Ops α) (input : Nat → Nat → α) (offset : α) (row tid iteration : Nat) (acc : α) : α :=
  expStoreFold ops input offset row tid iteration 0 8 acc

def expRoundCost (tid iteration : Nat) : Nat := expBufferCost tid iteration+expStoresCost tid iteration 0 8+3

theorem exp_round_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) (ht : tid<1024)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    ExpRoundReady p input row tid (iteration+1) t offset (expRoundFold ops input offset row tid iteration acc)
      (expRoundState ops input offset row tid iteration t acc s) :=
  exp_store_finish_ready p ops input row tid iteration t offset _ _
    (exp_stores_ready p ops input offset row tid iteration t 0 8 acc _ ht
      (exp_buffer_ready p ops input row tid iteration t offset acc s ready))

theorem exp_round_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t extra : Nat) (acc : α) (s : State α) (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7)
    (ready : ExpRoundReady p input row tid iteration t offset acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+expRoundCost tid iteration) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expRoundState ops input offset row tid iteration t acc s) := by
  have buffered := exp_buffer_ready p ops input row tid iteration t offset acc s ready
  have stored := exp_stores_ready p ops input offset row tid iteration t 0 8 acc _ ht buffered
  rewrite [show extra+expRoundCost tid iteration=((extra+3)+expStoresCost tid iteration 0 8)+expBufferCost tid iteration by
    unfold expRoundCost; omega]
  rewrite [exp_buffer_eq p guarded ops input row tid iteration t _ offset acc s hr ht hi ready]
  rewrite [exp_stores_eq p guarded ops input offset row tid iteration t 0 8 (extra+3) acc _ hr ht hi (by decide) buffered]
  exact exp_store_finish_eq p guarded ops t tid iteration extra _ ht hi stored.pc stored.baseIndex stored.componentIndex

theorem exp_round_trace_length (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (expRoundState ops input offset row tid iteration t acc s).trace.length=
      s.trace.length+16+2*expStoresCount tid iteration 0 8 := by
  change (expStoreFinish t tid iteration _).trace.length=_
  rewrite [(exp_store_finish_fields t tid iteration _).2.2.2.2.2,exp_stores_trace_length,exp_buffer_trace_length]
  omega

theorem exp_round_epochs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (expRoundState ops input offset row tid iteration t acc s).epochs=s.epochs :=
  (exp_store_finish_fields t tid iteration _).2.2.2.2.1.trans
    ((exp_stores_epochs ops input offset row tid iteration t 0 8 acc _).trans (exp_buffer_epochs ops input row tid iteration t s))

theorem exp_round_index_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t r : Nat) (acc : α) (s : State α)
    (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (expRoundState ops input offset row tid iteration t acc s).indices t r=s.indices t r :=
  (exp_store_finish_index_other t tid iteration r _ h9).trans
    ((exp_stores_index_other ops input offset row tid iteration t 0 8 r acc _ h13 h14 h15).trans
      (exp_buffer_index_other ops input row tid iteration t r s h10 h11 h12 h13))

theorem exp_round_memory_frame (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ t ∨ l.buffer ≠ 0)
    (houtput : ∀ component, component<8 → column tid iteration component<50257 →
      l ≠ globalCell 0 (address row (column tid iteration component))) :
    (expRoundState ops input offset row tid iteration t acc s).memory l=s.memory l :=
  (exp_stores_memory_frame ops input offset row tid iteration t 0 8 acc _ l
    (by intro slot _ hs hcol; exact houtput slot hs hcol)).trans
    (exp_buffer_memory_other ops input row tid iteration t s l hprivate)

theorem exp_round_outputs (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    ExpOutputs ops input offset row tid iteration 8 (expRoundState ops input offset row tid iteration t acc s) :=
  exp_stores_outputs ops input offset row tid iteration t 0 8 acc _ (by intro component hc; omega)

theorem exp_round_cost_bound (tid iteration : Nat) : expRoundCost tid iteration≤151 := by
  have a := exp_buffer_cost_bound tid iteration
  have b := exp_stores_cost_bound tid iteration 0 8
  unfold expRoundCost
  omega

#print axioms exp_buffer_index_other
#print axioms exp_buffer_epochs
#print axioms exp_store_finish_eq
#print axioms exp_store_finish_fields
#print axioms exp_store_finish_index_other
#print axioms exp_store_finish_ready
#print axioms exp_round_ready
#print axioms exp_round_eq
#print axioms exp_round_trace_length
#print axioms exp_round_epochs
#print axioms exp_round_index_other
#print axioms exp_round_memory_frame
#print axioms exp_round_outputs
#print axioms exp_round_cost_bound
end LarkNativeSoftmax
