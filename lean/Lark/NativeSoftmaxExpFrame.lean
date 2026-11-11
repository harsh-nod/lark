import Lark.NativeSoftmaxExpPrefixCounts

/-! Control and memory frames needed to compose actual lane prefixes. A lane
preserves every other lane's controls, input, shared maximum and output cells
owned by different threads. Scheduler/wave execution is a separate obligation. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exp_load_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expLoadAfter ops input row tid iteration component t s) := by
  by_cases hc : 50257≤column tid iteration component <;>
    simp [OtherThread,expLoadAfter,expLoadHead,expLoadTail,expLoadStored,expLoadAdvance,
      expClampedState,hc,setIndex,written,record,advance,hu]

theorem exp_loads_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component count u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expLoads ops input row tid iteration t component count s) := by
  induction count generalizing component s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (exp_load_other ops input row tid iteration component t u s hu)
      (ih (component+1) (expLoadAfter ops input row tid iteration component t s))

theorem exp_load_begin_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expLoadBegin t s) := by simp [OtherThread,expLoadBegin,setIndex,advance,hu]

theorem exp_load_finish_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expLoadFinish t s) := by simp [OtherThread,expLoadFinish,setIndex,advance,hu]

theorem exp_buffer_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expBufferState ops input row tid iteration t s) :=
  other_thread_trans t u _ _ _ (exp_load_begin_other t u s hu)
    (other_thread_trans t u _ _ _ (exp_loads_other ops input row tid iteration t 0 8 u (expLoadBegin t s) hu)
      (exp_load_finish_other t u _ hu))

theorem exp_store_head_other (tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreHead tid iteration component t s) := by
  simp [OtherThread,expStoreHead,setIndex,advance,hu]

theorem exp_store_next_other (t component u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreNext t component s) := by simp [OtherThread,expStoreNext,setIndex,advance,hu]

theorem exp_store_body_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreBody ops input offset acc row tid iteration component t s) :=
  other_thread_trans t u _ _ _
    (exp_store_values_other ops (expInputValue ops input row tid iteration component) offset t component u s hu)
    (exp_store_emit_other ops (expComponentValue ops input offset row tid iteration component) acc
      row (column tid iteration component) t u _ hu)

theorem exp_store_middle_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreMiddle ops input offset acc row tid iteration component t s) := by
  by_cases hc : column tid iteration component<50257
  · simp only [expStoreMiddle,if_pos hc]
    exact other_thread_trans t u _ _ _ (exp_store_head_other tid iteration component t u s hu)
      (exp_store_body_other ops input offset acc row tid iteration component t u _ hu)
  · simpa only [expStoreMiddle,if_neg hc] using exp_store_head_other tid iteration component t u s hu

theorem exp_store_after_other (ops : Ops α) (input : Nat → Nat → α) (offset acc : α)
    (row tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreAfter ops input offset acc row tid iteration component t s) :=
  other_thread_trans t u _ _ _ (exp_store_middle_other ops input offset acc row tid iteration component t u s hu)
    (exp_store_next_other t component u _ hu)

theorem exp_stores_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t component count u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStores ops input offset row tid iteration t component count acc s) := by
  induction count generalizing component acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (exp_store_after_other ops input offset acc row tid iteration component t u s hu)
      (ih (component+1) (expStoreAcc ops input offset acc row tid iteration component)
        (expStoreAfter ops input offset acc row tid iteration component t s))

theorem exp_store_finish_other (t tid iteration u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expStoreFinish t tid iteration s) := by simp [OtherThread,expStoreFinish,setIndex,advance,hu]

theorem exp_round_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid iteration t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expRoundState ops input offset row tid iteration t acc s) :=
  other_thread_trans t u _ _ _ (exp_buffer_other ops input row tid iteration t u s hu)
    (other_thread_trans t u _ _ _
      (exp_stores_other ops input offset row tid iteration t 0 8 u acc (expBufferState ops input row tid iteration t s) hu)
      (exp_store_finish_other t tid iteration u _ hu))

theorem exp_rounds_other (ops : Ops α) (input : Nat → Nat → α) (offset : α)
    (row tid t iteration count u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expRounds ops input offset row tid t iteration count acc s) := by
  induction count generalizing iteration acc s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih =>
    exact other_thread_trans t u _ _ _ (exp_round_other ops input offset row tid iteration t u acc s hu)
      (ih (iteration+1) (expRoundFold ops input offset row tid iteration acc)
        (expRoundState ops input offset row tid iteration t acc s))

theorem exp_exit_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (expExit ops t s) := by simp [OtherThread,expExit,setReg,advance,hu]

theorem exp_prefix_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid u : Nat) (s : State α) (hu : u ≠ row*1024+tid) :
    OtherThread (row*1024+tid) u s (expPrefixState ops input row tid s) :=
  other_thread_trans (row*1024+tid) u _ _ _ (exp_start_other ops (rowMaximum ops input row) (row*1024+tid) tid u s hu)
    (other_thread_trans (row*1024+tid) u _ _ _
      (exp_rounds_other ops input (rowMaximum ops input row) row tid (row*1024+tid) 0 7 u (ops.literal 0 1)
        (expStart ops (rowMaximum ops input row) (row*1024+tid) tid s) hu)
      (exp_exit_other ops (row*1024+tid) u _ hu))

theorem exp_prefix_native_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid u : Nat) (s : State α) (hu : u ≠ row*1024+tid) (hi : MaxNativeIndices u s) :
    MaxNativeIndices u (expPrefixState ops input row tid s) := by
  have hf := (exp_prefix_other ops input row tid u s hu).2.1
  exact ⟨(congrArg (fun indices => indices 0) hf).trans hi.1,
    (congrArg (fun indices => indices 1) hf).trans hi.2.1,
    (congrArg (fun indices => indices 2) hf).trans hi.2.2.1,
    (congrArg (fun indices => indices 3) hf).trans hi.2.2.2⟩

theorem exp_prefix_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (reads : Reads p input s) : Reads p input (expPrefixState ops input row tid s) := by
  intro offset hb
  apply (exp_prefix_memory_frame ops input row tid s (globalCell 1 offset)
    (Or.inl (by change Space.global ≠ Space.local; decide)) ?_).trans (reads offset hb)
  intro iteration hi component hc hcol h
  have hf := congrArg Location.buffer h
  simp [globalCell] at hf

theorem exp_prefix_shared_maximum (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (hm : s.memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row)) :
    (expPrefixState ops input row tid s).memory ⟨.shared,row,0,0⟩=some (rowMaximum ops input row) := by
  apply (exp_prefix_memory_frame ops input row tid s ⟨.shared,row,0,0⟩
    (Or.inl (by change Space.shared ≠ Space.local; decide)) ?_).trans hm
  intro iteration hi component hc hcol h
  have hs := congrArg Location.space h
  simp [globalCell] at hs

theorem exp_prefix_output_other_thread (ops : Ops α) (input : Nat → Nat → α)
    (row tid offset : Nat) (s : State α) (ht : tid<1024) (ho : writer offset ≠ row*1024+tid) :
    (expPrefixState ops input row tid s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  apply exp_prefix_memory_frame ops input row tid s (globalCell 0 offset)
    (Or.inl (by change Space.global ≠ Space.local; decide))
  intro iteration hi component hc hcol h
  have he := congrArg Location.offset h
  change offset=address row (column tid iteration component) at he
  apply ho
  rewrite [he]
  exact address_writer row tid iteration component ht hcol

#print axioms exp_load_other
#print axioms exp_loads_other
#print axioms exp_load_begin_other
#print axioms exp_load_finish_other
#print axioms exp_buffer_other
#print axioms exp_store_head_other
#print axioms exp_store_next_other
#print axioms exp_store_body_other
#print axioms exp_store_middle_other
#print axioms exp_store_after_other
#print axioms exp_stores_other
#print axioms exp_store_finish_other
#print axioms exp_round_other
#print axioms exp_rounds_other
#print axioms exp_exit_other
#print axioms exp_prefix_other
#print axioms exp_prefix_native_other
#print axioms exp_prefix_reads
#print axioms exp_prefix_shared_maximum
#print axioms exp_prefix_output_other_thread
end LarkNativeSoftmax
