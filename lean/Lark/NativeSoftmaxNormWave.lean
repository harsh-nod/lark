import Lark.NativeSoftmaxNormCohortFrame

/-! Actual final normalization phase of a physical wave64. All lanes halt at
the source-specific final PC; no shuffle or extra synchronization is inserted. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_cohort_halt (guarded : Bool) (row warp active : Nat) (s : State α)
    (hpos : 0<active) (hp : ∀ lane, lane<active → s.pc (cohortBase row warp+lane)=normPc guarded 115) :
    LarkPartitionCollective.nextCohort (program guarded) (cohortThreads row warp active) s=none ∧
    LarkCollective.converged (program guarded) (cohortThreads row warp active) s=some .halt := by
  have hp0 : s.pc (cohortBase row warp)=normPc guarded 115 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp active).filter (LarkPartitionCollective.isShuffle (program guarded) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [LarkPartitionCollective.isShuffle,hp lane hl,(norm_round_end_codes guarded).2.2]
  have ha : (cohortThreads row warp active).all (fun t => s.pc t == s.pc (cohortBase row warp))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [hp lane hl,hp0]
  constructor
  · simp [LarkPartitionCollective.nextCohort,hf]
  · unfold LarkCollective.converged
    rewrite [cohort_head row warp active hpos]
    simp only [bind,pure,Option.bind,ha,↓reduceIte]
    unfold LarkCollective.parked
    rewrite [hp0,(norm_round_end_codes guarded).2.2]
    rfl

def normWave (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  normScalarFold guarded ops input row (cohortThreads row warp 64) s

theorem norm_wave_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) :
    (normWave guarded ops input row warp s).pc (cohortBase row warp+lane)=normPc guarded 115 :=
  norm_scalar_fold_member_pc guarded ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw) _
    ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem norm_wave_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (entry : NormCohortEntry p ops input row (cohortThreads row warp 64) s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s=some (normWave guarded ops input row warp s) := by
  have hfold := norm_scalar_fold_run p guarded ops input row (cohortThreads row warp 64) s
    (cohort_nodup row warp 64) (exp_cohort_row row warp hw) entry
  change _=some (normWave guarded ops input row warp s) at hfold
  have hhalt := norm_cohort_halt guarded row warp 64 (normWave guarded ops input row warp s) (by decide)
    (by intro lane hl; exact norm_wave_pc guarded ops input row warp lane s hw hl)
  rewrite [cohort_native_threads p row warp hw,show fuel.warp=7+1 by decide,LarkPartitionCollective.runWarp,hfold]
  simp only [bind,pure,Option.some_bind,hhalt.1,hhalt.2,reduceCtorEq,↓reduceIte]

theorem norm_wave_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) : (normWave guarded ops input row warp s).epochs=s.epochs :=
  norm_scalar_fold_epochs guarded ops input row _ s

theorem norm_wave_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (hw : warp<16) (ht : t ∉ cohortThreads row warp 64) :
    OtherThread t t s (normWave guarded ops input row warp s) :=
  norm_scalar_fold_other guarded ops input row _ t s ht (exp_cohort_row row warp hw)

theorem norm_wave_entry_other (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t : Nat) (s : State α) (hw : warp<16) (ht : t ∉ cohortThreads row warp 64) (hrow : t/1024=row)
    (entry : NormCohortEntry p ops input row (cohortThreads row warp 64) s) (next : NormLaneEntry p ops input row (t%1024) s) :
    NormLaneEntry p ops input row (t%1024) (normWave guarded ops input row warp s) :=
  norm_scalar_fold_entry_other p guarded ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw) entry t ht hrow next

theorem norm_wave_output_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp offset : Nat) (s : State α) (hw : warp<16) (ho : writer offset ∉ cohortThreads row warp 64) :
    (normWave guarded ops input row warp s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) :=
  norm_scalar_fold_output_other guarded ops input row _ offset s (exp_cohort_row row warp hw) ho

theorem norm_wave_output_value (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t iteration component : Nat) (s : State α) (hw : warp<16) (ht : t ∈ cohortThreads row warp 64)
    (hi : iteration<7) (hc : component<8) (hcol : column (t%1024) iteration component<50257) :
    (normWave guarded ops input row warp s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (normOutputValue ops input row (column (t%1024) iteration component)) :=
  norm_scalar_fold_output_member guarded ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw)
    t iteration component ht hi hc hcol

theorem norm_wave_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (entry : NormCohortEntry p ops input row (cohortThreads row warp 64) s)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (normWave true ops input row warp s).trace, Good a :=
  norm_scalar_fold_fixed_good p ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw) entry good

theorem norm_wave_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (normWave guarded ops input row warp s).trace.length=s.trace.length+normScalarAccesses guarded (cohortThreads row warp 64) :=
  norm_scalar_fold_trace_length guarded ops input row _ s

#print axioms norm_cohort_halt
#print axioms norm_wave_pc
#print axioms norm_wave_run
#print axioms norm_wave_epochs
#print axioms norm_wave_other
#print axioms norm_wave_entry_other
#print axioms norm_wave_output_other
#print axioms norm_wave_output_value
#print axioms norm_wave_fixed_good
#print axioms norm_wave_trace_length
end LarkNativeSoftmax
