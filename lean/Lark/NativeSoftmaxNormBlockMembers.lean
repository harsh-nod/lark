import Lark.NativeSoftmaxNormLaneMembers

/-! Membership of selected source accesses in the actual sequential native64
cohort and block folds. The folds preserve every epoch map and only extend the
trace, so events survive all later lanes and waves. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_scalar_event_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (t : Nat) (event : (Nat → Epoch) → Access)
    (s : State α) (ht : t∈ts)
    (hit : ∀ state : State α, event state.epochs ∈ (normLaneStep guarded ops input row t state).trace) :
    event s.epochs ∈ (normScalarFold guarded ops input row ts s).trace :=
  norm_scheduler_fold_event_member (fun u state => normLaneStep guarded ops input row u state) ts t event
    (fun u state => norm_lane_trace_grows guarded ops input row (u%1024) state)
    (fun u state => norm_lane_epochs guarded ops input row (u%1024) state) hit s ht

theorem norm_waves_event_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (warp : Nat) (event : (Nat → Epoch) → Access)
    (s : State α) (hw : warp∈ws)
    (hit : ∀ state : State α, event state.epochs ∈ (normWave guarded ops input row warp state).trace) :
    event s.epochs ∈ (normWaveFold guarded ops input row ws s).trace :=
  norm_scheduler_fold_event_member (fun w state => normWave guarded ops input row w state) ws warp event
    (fun w state => norm_scalar_fold_trace_grows guarded ops input row (cohortThreads row w 64) state)
    (fun w state => norm_scalar_fold_epochs guarded ops input row (cohortThreads row w 64) state) hit s hw

theorem norm_wave_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row warp tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (hm : row*1024+tid∈cohortThreads row warp 64) :
    normReadAccess row tid iteration component s.epochs ∈ (normWave false ops input row warp s).trace := by
  have hmod : (row*1024+tid)%1024=tid := by omega
  exact norm_scalar_event_member false ops input row (cohortThreads row warp 64) (row*1024+tid)
    (normReadAccess row tid iteration component) s hm (fun state => by
      simpa only [normLaneStep,hmod] using norm_lane_original_member ops input row tid iteration component state hi hc)

theorem norm_wave_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257)
    (hm : row*1024+tid∈cohortThreads row warp 64) :
    normWriteAccess row tid iteration component s.epochs ∈ (normWave guarded ops input row warp s).trace := by
  have hmod : (row*1024+tid)%1024=tid := by omega
  exact norm_scalar_event_member guarded ops input row (cohortThreads row warp 64) (row*1024+tid)
    (normWriteAccess row tid iteration component) s hm (fun state => by
      simpa only [normLaneStep,hmod] using norm_lane_valid_member guarded ops input row tid iteration component state hi hc hcol)

theorem norm_block_original_member (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) :
    normReadAccess row tid iteration component s.epochs ∈ (normBlock false ops input row s).trace := by
  have hm : row*1024+tid∈cohortThreads row (tid/64) 64 := by
    apply (cohort_mem row (tid/64) 64 _).mpr
    refine ⟨tid%64,Nat.mod_lt _ (by decide),?_⟩
    unfold cohortBase
    omega
  exact norm_waves_event_member false ops input row (List.range 16) (tid/64)
    (normReadAccess row tid iteration component) s (List.mem_range.mpr (by omega))
    (fun state => norm_wave_original_member ops input row (tid/64) tid iteration component state ht hi hc hm)

theorem norm_block_valid_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component s.epochs ∈ (normBlock guarded ops input row s).trace := by
  have hm : row*1024+tid∈cohortThreads row (tid/64) 64 := by
    apply (cohort_mem row (tid/64) 64 _).mpr
    refine ⟨tid%64,Nat.mod_lt _ (by decide),?_⟩
    unfold cohortBase
    omega
  exact norm_waves_event_member guarded ops input row (List.range 16) (tid/64)
    (normWriteAccess row tid iteration component) s (List.mem_range.mpr (by omega))
    (fun state => norm_wave_valid_member guarded ops input row (tid/64) tid iteration component state ht hi hc hcol hm)

#print axioms norm_scalar_event_member
#print axioms norm_waves_event_member
#print axioms norm_wave_original_member
#print axioms norm_wave_valid_member
#print axioms norm_block_original_member
#print axioms norm_block_valid_member
end LarkNativeSoftmax
