import Lark.NativeSoftmaxNormTraceGrowth

/-! Selected original normalization reads and valid output writes occur in
their actual component folds. The epoch is the incoming state epoch, since
normalization performs no synchronization. No intermediate-state reachability
is assumed; later composition will instantiate the proved complete block. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normReadAccess (row tid iteration component : Nat) (epochs : Nat → Epoch) : Access :=
  ⟨row*1024+tid,globalCell 0 (address row (normSelectedColumn false (column tid iteration component))),
    false,epochs (row*1024+tid)⟩

def normWriteAccess (row tid iteration component : Nat) (epochs : Nat → Epoch) : Access :=
  ⟨row*1024+tid,globalCell 0 (address row (column tid iteration component)),true,epochs (row*1024+tid)⟩

theorem norm_original_read_member (ops : Ops α) (row tid iteration component : Nat) (s : State α) :
    normReadAccess row tid iteration component s.epochs ∈
      (normLoadState false ops row tid iteration component (row*1024+tid) s).trace := by
  rewrite [norm_load_component_trace]
  simp [normReadAccess]

theorem norm_valid_write_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hc : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈
      (normStoreAfter guarded ops input row tid iteration component s).trace := by
  rewrite [norm_store_component_trace,if_pos hc]
  exact List.mem_cons_self

theorem norm_loads_original_member (ops : Ops α) (row tid iteration start count component : Nat)
    (s : State α) (hlo : start≤component) (hhi : component<start+count) :
    normReadAccess row tid iteration component s.epochs ∈
      (normLoads false ops row tid iteration start count s).trace := by
  induction count generalizing start s with
  | zero => omega
  | succ count ih =>
    let head := normLoadState false ops row tid iteration start (row*1024+tid) s
    change normReadAccess row tid iteration component s.epochs ∈
      (normLoads false ops row tid iteration (start+1) count head).trace
    by_cases he : component=start
    · subst component
      exact norm_loads_trace_grows false ops row tid iteration (start+1) count head _
        (norm_original_read_member ops row tid iteration start s)
    · have hm := ih (start+1) head (by omega) (by omega)
      simpa only [head,norm_load_component_epochs] using hm

theorem norm_stores_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration start count component : Nat) (s : State α)
    (hlo : start≤component) (hhi : component<start+count) (hc : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈
      (normStores guarded ops input row tid iteration start count s).trace := by
  induction count generalizing start s with
  | zero => omega
  | succ count ih =>
    let head := normStoreAfter guarded ops input row tid iteration start s
    change normWriteAccess row tid iteration component s.epochs ∈
      (normStores guarded ops input row tid iteration (start+1) count head).trace
    by_cases he : component=start
    · subst component
      exact norm_stores_trace_grows guarded ops input row tid iteration (start+1) count head _
        (norm_valid_write_member guarded ops input row tid iteration start s hc)
    · have hm := ih (start+1) head (by omega) (by omega)
      simpa only [head,norm_store_component_epochs] using hm

#print axioms norm_original_read_member
#print axioms norm_valid_write_member
#print axioms norm_loads_original_member
#print axioms norm_stores_valid_member
end LarkNativeSoftmax
