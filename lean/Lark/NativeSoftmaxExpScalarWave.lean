import Lark.NativeSoftmaxExpCohort

/-! Actual scalar lane-fold for a physical64 cohort, from the proved maximum
state to PC70 in every lane. This does not execute the pending sum shuffles. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expScalarWave (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  expScalarFold ops input row (cohortThreads row warp 64) s

theorem exp_cohort_entry_of_maximum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    ExpCohortEntry p ops input row (cohortThreads row warp 64) s := by
  exact {
    valid := ready.valid
    pc := by
      intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
      simpa only [cohortBase,Nat.add_assoc] using ready.pc (warp*64+lane) (by omega)
    native := by
      intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
      simpa only [cohortBase,Nat.add_assoc] using ready.indices (warp*64+lane) (by omega)
    maximum := ready.maximum
    reads := ready.reads
    epoch := by
      intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
      simpa only [cohortBase,Nat.add_assoc] using ready.epoch (warp*64+lane) (by omega)
    good := ready.good }

theorem exp_cohort_row (row warp : Nat) (hw : warp<16) : ∀ t ∈ cohortThreads row warp 64, t/1024=row := by
  intro t ht
  obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
  exact (cohort_arithmetic row warp lane hw hl).1

theorem exp_scalar_wave_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    (warpThreads (geometry p) row warp).foldlM
      (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t fuel.lane s) s=
      some (expScalarWave ops input row warp s) := by
  rewrite [cohort_native_threads p row warp hw]
  exact exp_scalar_fold_run p guarded ops input row _ s (cohort_nodup row warp 64)
    (exp_cohort_row row warp hw) (exp_cohort_entry_of_maximum p ops input row warp s hw ready)

theorem exp_scalar_wave_pc (ops : Ops α) (input : Nat → Nat → α) (row warp lane : Nat) (s : State α)
    (hw : warp<16) (hl : lane<64) : (expScalarWave ops input row warp s).pc (cohortBase row warp+lane)=70 :=
  exp_scalar_fold_member_pc ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw)
    _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem exp_scalar_wave_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) (ready : MaximumReady p ops input row s) :
    (expScalarWave ops input row warp s).regs (cohortBase row warp+lane) 6=
      some (threadExpSum ops input row (warp*64+lane)) := by
  have h := exp_scalar_fold_member_sum p ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw)
    (exp_cohort_entry_of_maximum p ops input row warp s hw ready) _ ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)
  simpa only [(cohort_arithmetic row warp lane hw hl).2.1] using h

theorem exp_scalar_wave_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    ∀ a ∈ (expScalarWave ops input row warp s).trace, Good a :=
  exp_scalar_fold_good p ops input row _ s (cohort_nodup row warp 64) (exp_cohort_row row warp hw)
    (exp_cohort_entry_of_maximum p ops input row warp s hw ready)

theorem exp_scalar_wave_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) (ready : MaximumReady p ops input row s) :
    raceFree (geometry p) (expScalarWave ops input row warp s).trace=true :=
  race_free p _ (exp_scalar_wave_good p ops input row warp s hw ready)

#print axioms exp_cohort_entry_of_maximum
#print axioms exp_cohort_row
#print axioms exp_scalar_wave_run
#print axioms exp_scalar_wave_pc
#print axioms exp_scalar_wave_sum
#print axioms exp_scalar_wave_good
#print axioms exp_scalar_wave_race_free
end LarkNativeSoftmax
