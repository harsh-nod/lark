import Lark.NativeSoftmaxNormBufferFrame

/-! One complete actual normalization outer iteration for both bound sources.
The false store-loop exit increments the outer index and returns to PC95.
Every valid output retains the explicit half-conversion/division formula. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStoreFinish (guarded : Bool) (t tid iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t (normPc guarded 113)) t 17 ((base tid (iteration+1) : Nat) : Int) (normPc guarded 114)) t 95

theorem norm_store_finish_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α) (ht : tid<1024) (hi : iteration<7)
    (hp : s.pc t=normPc guarded 105) (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int))
    (h21 : s.indices t 21=some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normStoreFinish guarded t tid iteration s) := by
  let s1 := advance s t (normPc guarded 113)
  let s2 := setIndex s1 t 17 ((base tid (iteration+1) : Nat) : Int) (normPc guarded 114)
  have pred := predicate_nlt_of (geometry p) t s (.ivar 21) (.const 8) 8 8 h21 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 21) (.const 8)) (normPc guarded 113)) s=some s1 := by
    simp [execute,pred,hp,s1]
  have hb : base tid iteration+8192<2147483648 := by unfold base; omega
  have ix := eval_nat_sum (geometry p) t (base tid iteration) 8192 s1 (.ivar 17) (.const 8192) h17 rfl hb
  have hbase : base tid iteration+8192=base tid (iteration+1) := by simp [base,Nat.add_mul]; omega
  have ix' : evalIndex (geometry p) t s1 (.add (.ivar 17) (.const 8192))=some ((base tid (iteration+1) : Nat) : Int) := by
    simpa only [hbase] using ix
  have e2 := execute_index_of ops (layout p) (geometry p) t 17 (normPc guarded 114) (.add (.ivar 17) (.const 8192)) s1 _ ix'
    (by simp only [s1,advance,↓reduceIte]; exact (norm_pc_next guarded 113).symm)
  change execute _ _ _ _ _ s1=some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 95) s2=some (normStoreFinish guarded t tid iteration s) := rfl
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 105) _ _ s s1 (norm_store_head_codes guarded).1 hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 113) _ _ s1 s2 (norm_round_end_codes guarded).1 (by simp [s1,advance]) e2]
  exact scalar_step p guarded ops t (normPc guarded 114) extra _ s2 _ (norm_round_end_codes guarded).2.1
    (by simp [s2,setIndex,advance]) e3

theorem norm_store_finish_fields (guarded : Bool) (t tid iteration : Nat) (s : State α) :
    (normStoreFinish guarded t tid iteration s).pc t=95 ∧
    (normStoreFinish guarded t tid iteration s).indices t 17=some ((base tid (iteration+1) : Nat) : Int) ∧
    (normStoreFinish guarded t tid iteration s).memory=s.memory ∧
    (normStoreFinish guarded t tid iteration s).regs=s.regs ∧
    (normStoreFinish guarded t tid iteration s).epochs=s.epochs ∧
    (normStoreFinish guarded t tid iteration s).trace=s.trace := by simp [normStoreFinish,setIndex,advance]

theorem norm_store_finish_index_other (guarded : Bool) (t tid iteration r : Nat) (s : State α) (hr : r ≠ 17) :
    (normStoreFinish guarded t tid iteration s).indices t r=s.indices t r := by simp [normStoreFinish,setIndex,advance,hr]

theorem norm_store_finish_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (ready : NormStoreReady p guarded ops input row tid iteration 8 s) :
    NormRoundReady p ops input row tid (iteration+1) (normStoreFinish guarded (row*1024+tid) tid iteration s) := by
  obtain ⟨hp,h17,hm,hr,he,_⟩ := norm_store_finish_fields guarded (row*1024+tid) tid iteration s
  have idx := norm_store_finish_index_other (α := α) guarded (row*1024+tid) tid iteration
  exact {
    valid := ready.valid
    bound := ready.bound
    pc := hp
    native := ⟨(idx 0 s (by decide)).trans ready.native.1,(idx 1 s (by decide)).trans ready.native.2.1,
      (idx 2 s (by decide)).trans ready.native.2.2.1,(idx 3 s (by decide)).trans ready.native.2.2.2⟩
    base := h17
    denominator := (congrArg (fun regs => regs (row*1024+tid) 12) hr).trans ready.denominator
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block) he).trans ready.epoch
    future := norm_future_memory ops input row tid (iteration+1) s _ hm ready.future
    present := norm_present_memory row s _ hm ready.present }

def normRoundState (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) : State α :=
  normStoreFinish guarded (row*1024+tid) tid iteration
    (normStores guarded ops input row tid iteration 0 8 (normBufferState guarded ops row tid iteration s))

def normRoundCost (guarded : Bool) (tid iteration : Nat) : Nat :=
  normBufferCost guarded tid iteration+normStoresCost tid iteration 0 8+3

theorem norm_round_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (hi : iteration<7) (ready : NormRoundReady p ops input row tid iteration s) :
    NormRoundReady p ops input row tid (iteration+1) (normRoundState guarded ops input row tid iteration s) :=
  norm_store_finish_ready p guarded ops input row tid iteration _
    (norm_stores_ready p guarded ops input row tid iteration 0 8 _ (by decide)
      (norm_buffer_ready p guarded ops input row tid iteration s hi ready))

theorem norm_round_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration extra : Nat) (s : State α) (hi : iteration<7) (ready : NormRoundReady p ops input row tid iteration s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) (extra+normRoundCost guarded tid iteration) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) (row*1024+tid) extra
        (normRoundState guarded ops input row tid iteration s) := by
  have buffered := norm_buffer_ready p guarded ops input row tid iteration s hi ready
  have stored := norm_stores_ready p guarded ops input row tid iteration 0 8 _ (by decide) buffered
  rewrite [show extra+normRoundCost guarded tid iteration=((extra+3)+normStoresCost tid iteration 0 8)+normBufferCost guarded tid iteration by
    unfold normRoundCost; omega,
    norm_buffer_eq p guarded ops input row tid iteration _ s hi ready,
    norm_stores_eq p guarded ops input row tid iteration 0 8 (extra+3) _ hi (by decide) buffered]
  exact norm_store_finish_eq p guarded ops (row*1024+tid) tid iteration extra _ ready.bound hi stored.pc stored.base stored.componentIndex

theorem norm_round_outputs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) : NormOutputs ops input row tid iteration 8 (normRoundState guarded ops input row tid iteration s) := by
  intro c hc hcol
  dsimp only [normRoundState]
  rewrite [(norm_store_finish_fields guarded (row*1024+tid) tid iteration _).2.2.1]
  exact norm_stores_outputs guarded ops input row tid iteration 0 8 _ (by intro c hc; omega) c hc hcol

theorem norm_round_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) : (normRoundState guarded ops input row tid iteration s).epochs=s.epochs :=
  (norm_store_finish_fields guarded (row*1024+tid) tid iteration _).2.2.2.2.1.trans
    ((norm_stores_epochs guarded ops input row tid iteration 0 8 _).trans (norm_buffer_epochs guarded ops row tid iteration s))

theorem norm_round_denominator (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) :
    (normRoundState guarded ops input row tid iteration s).regs (row*1024+tid) 12=s.regs (row*1024+tid) 12 :=
  (congrArg (fun regs => regs (row*1024+tid) 12)
    (norm_store_finish_fields guarded (row*1024+tid) tid iteration _).2.2.2.1).trans
      ((norm_stores_denominator guarded ops input row tid iteration 0 8 _).trans
        (congrArg (fun regs => regs (row*1024+tid) 12) (norm_buffer_regs guarded ops row tid iteration s)))

theorem norm_round_index_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration r : Nat) (s : State α)
    (h17 : r ≠ 17) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) (h21 : r ≠ 21) (h22 : r ≠ 22) (h23 : r ≠ 23) :
    (normRoundState guarded ops input row tid iteration s).indices (row*1024+tid) r=s.indices (row*1024+tid) r :=
  (norm_store_finish_index_other guarded (row*1024+tid) tid iteration r _ h17).trans
    ((norm_stores_index_other guarded ops input row tid iteration 0 8 r _ h21 h22 h23).trans
      (norm_buffer_index_other guarded ops row tid iteration r s h18 h19 h20 h21))

theorem norm_round_memory_frame (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (l : Location)
    (hprivate : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 1)
    (houtput : ∀ c, c<8 → column tid iteration c<50257 → l ≠ globalCell 0 (address row (column tid iteration c))) :
    (normRoundState guarded ops input row tid iteration s).memory l=s.memory l :=
  (congrFun (norm_store_finish_fields guarded (row*1024+tid) tid iteration _).2.2.1 l).trans
    ((norm_stores_memory_frame guarded ops input row tid iteration 0 8 _ l (by
      intro c _ hc hcol; exact houtput c hc hcol)).trans
      (norm_buffer_memory_other guarded ops row tid iteration s l hprivate))

theorem norm_round_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) :
    (normRoundState guarded ops input row tid iteration s).trace.length=
      s.trace.length+2*normLoadsCount guarded tid iteration 0 8+2*normStoresCount tid iteration 0 8 := by
  change (normStoreFinish guarded (row*1024+tid) tid iteration _).trace.length=_
  rewrite [(norm_store_finish_fields guarded (row*1024+tid) tid iteration _).2.2.2.2.2,norm_stores_trace_length,norm_buffer_trace_length]
  rfl

theorem norm_round_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normRoundState guarded ops input row tid iteration s) := by
  have hf : OtherThread (row*1024+tid) u
      (normStores guarded ops input row tid iteration 0 8 (normBufferState guarded ops row tid iteration s))
      (normRoundState guarded ops input row tid iteration s) := by
    simp [OtherThread,normRoundState,normStoreFinish,setIndex,advance,hu]
  exact other_thread_trans (row*1024+tid) u _ _ _ (norm_buffer_other guarded ops row tid iteration u s hu)
    (other_thread_trans (row*1024+tid) u _ _ _ (norm_stores_other guarded ops input row tid iteration 0 8 u _ hu) hf)

theorem norm_round_fixed_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normRoundState true ops input row tid iteration s).trace, Good a := by
  intro a ha
  change a ∈ (normStoreFinish true (row*1024+tid) tid iteration _).trace at ha
  rewrite [(norm_store_finish_fields true (row*1024+tid) tid iteration _).2.2.2.2.2] at ha
  exact norm_stores_good true ops input row tid iteration 0 8 _ ht (norm_buffer_fixed_good ops row tid iteration s ht good) a ha

theorem norm_round_cost_bound (guarded : Bool) (tid iteration : Nat) : normRoundCost guarded tid iteration≤135 := by
  have a := norm_buffer_cost_bound guarded tid iteration
  have b := norm_stores_cost_bound tid iteration 0 8
  unfold normRoundCost
  omega

#print axioms norm_store_finish_eq
#print axioms norm_store_finish_fields
#print axioms norm_store_finish_index_other
#print axioms norm_store_finish_ready
#print axioms norm_round_ready
#print axioms norm_round_eq
#print axioms norm_round_outputs
#print axioms norm_round_epochs
#print axioms norm_round_denominator
#print axioms norm_round_index_other
#print axioms norm_round_memory_frame
#print axioms norm_round_trace_length
#print axioms norm_round_other
#print axioms norm_round_fixed_good
#print axioms norm_round_cost_bound
end LarkNativeSoftmax
