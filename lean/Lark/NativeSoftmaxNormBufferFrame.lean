import Lark.NativeSoftmaxNormStoreLoop

/-! Memory, control, trace and repaired-access frames for the complete actual
normalization buffer phase. It changes only this lane's private bank1 and
scratch indices; every global input/output cell remains intact. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_load_component_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normLoadState guarded ops row tid iteration component t s) := by
  have hh := norm_load_head_other guarded tid iteration component t u s hu
  by_cases hl : guarded=false ∨ column tid iteration component<50257 <;>
    simpa [OtherThread,normLoadState,hl,normLoadAdvance,normLoadStored,normLoadAddress,setIndex,written,record,advance,hu] using hh

theorem norm_loads_other (guarded : Bool) (ops : Ops α)
    (row tid iteration component count u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normLoads guarded ops row tid iteration component count s) := by
  induction count generalizing component s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans (row*1024+tid) u _ _ _
      (norm_load_component_other guarded ops row tid iteration component (row*1024+tid) u s hu) (ih (component+1) _)

theorem norm_buffer_other (guarded : Bool) (ops : Ops α)
    (row tid iteration u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (normBufferState guarded ops row tid iteration s) := by
  have hb : OtherThread (row*1024+tid) u s (normLoadBegin (row*1024+tid) s) := by
    simp [OtherThread,normLoadBegin,setIndex,advance,hu]
  have hl := norm_loads_other guarded ops row tid iteration 0 8 u (normLoadBegin (row*1024+tid) s) hu
  let loaded := normLoads guarded ops row tid iteration 0 8 (normLoadBegin (row*1024+tid) s)
  have hf : OtherThread (row*1024+tid) u loaded (normLoadFinish guarded (row*1024+tid) loaded) := by
    simp [OtherThread,normLoadFinish,setIndex,advance,hu]
  exact other_thread_trans (row*1024+tid) u _ _ _ hb (other_thread_trans (row*1024+tid) u _ _ _ hl hf)

theorem norm_buffer_index_other (guarded : Bool) (ops : Ops α)
    (row tid iteration r : Nat) (s : State α) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) (h21 : r ≠ 21) :
    (normBufferState guarded ops row tid iteration s).indices (row*1024+tid) r=s.indices (row*1024+tid) r :=
  (norm_load_finish_index_other guarded (row*1024+tid) r _ h21).trans
    ((norm_loads_index_other guarded ops row tid iteration 0 8 r _ h18 h19 h20).trans
      (norm_load_begin_index_other (row*1024+tid) r s h18))

theorem norm_buffer_epochs (guarded : Bool) (ops : Ops α) (row tid iteration : Nat) (s : State α) :
    (normBufferState guarded ops row tid iteration s).epochs=s.epochs :=
  (norm_load_finish_fields guarded (row*1024+tid) _).2.2.2.1.trans
    ((norm_loads_epochs guarded ops row tid iteration 0 8 _).trans
      (norm_load_begin_fields (row*1024+tid) s).2.2.2.1)

theorem norm_buffer_regs (guarded : Bool) (ops : Ops α) (row tid iteration : Nat) (s : State α) :
    (normBufferState guarded ops row tid iteration s).regs=s.regs :=
  (norm_load_finish_fields guarded (row*1024+tid) _).2.2.2.2.1.trans
    ((norm_loads_regs guarded ops row tid iteration 0 8 _).trans
      (norm_load_begin_fields (row*1024+tid) s).2.2.2.2.1)

theorem norm_buffer_memory_other (guarded : Bool) (ops : Ops α)
    (row tid iteration : Nat) (s : State α) (l : Location)
    (hl : l.space ≠ .local ∨ l.owner ≠ row*1024+tid ∨ l.buffer ≠ 1) :
    (normBufferState guarded ops row tid iteration s).memory l=s.memory l :=
  (congrFun (norm_load_finish_fields guarded (row*1024+tid) _).2.2.1 l).trans
    ((norm_loads_memory_other guarded ops row tid iteration 0 8 _ l hl).trans
      (congrFun (norm_load_begin_fields (row*1024+tid) s).2.2.1 l))

theorem norm_buffer_trace_length (guarded : Bool) (ops : Ops α) (row tid iteration : Nat) (s : State α) :
    (normBufferState guarded ops row tid iteration s).trace.length=
      s.trace.length+2*normLoadsCount guarded tid iteration 0 8 := by
  change (normLoadFinish guarded (row*1024+tid) _).trace.length=_
  rewrite [(norm_load_finish_fields guarded (row*1024+tid) _).2.2.2.2.2,norm_loads_trace_length,
    (norm_load_begin_fields (row*1024+tid) s).2.2.2.2.2]
  rfl

theorem norm_buffer_fixed_good (ops : Ops α) (row tid iteration : Nat) (s : State α)
    (ht : tid<1024) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normBufferState true ops row tid iteration s).trace, Good a := by
  intro a ha
  change a ∈ (normLoadFinish true (row*1024+tid) _).trace at ha
  rewrite [(norm_load_finish_fields true (row*1024+tid) _).2.2.2.2.2] at ha
  exact norm_loads_fixed_good ops row tid iteration 0 8 _ ht (by
    rewrite [(norm_load_begin_fields (row*1024+tid) s).2.2.2.2.2]
    exact good) a ha

#print axioms norm_load_component_other
#print axioms norm_loads_other
#print axioms norm_buffer_other
#print axioms norm_buffer_index_other
#print axioms norm_buffer_epochs
#print axioms norm_buffer_regs
#print axioms norm_buffer_memory_other
#print axioms norm_buffer_trace_length
#print axioms norm_buffer_fixed_good
end LarkNativeSoftmax
