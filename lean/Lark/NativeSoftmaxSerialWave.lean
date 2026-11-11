import Lark.NativeSoftmaxSerialFold

/-! The actual native wave runner executes its serial-phase lane fold and
returns at the second block barrier. No shuffle or early block resume occurs. -/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem serial_cohort_leader (row warp : Nat) :
    row*1024 ∈ cohortThreads row warp 64 ↔ warp=0 := by
  constructor
  · intro h
    obtain ⟨lane,hl,he⟩ := (cohort_mem row warp 64 _).mp h
    unfold cohortBase at he
    omega
  · intro h; subst warp
    exact (cohort_mem row 0 64 _).mpr ⟨0,by decide,by simp [cohortBase]⟩

theorem serial_cohort_count (row warp : Nat) :
    leaderCount row (cohortThreads row warp 64) = if warp=0 then 1 else 0 := by
  unfold leaderCount cohortThreads
  rewrite [List.countP_map]
  have he : (fun lane => cohortBase row warp+lane == row*1024) =
      (fun lane => if warp=0 then lane==0 else false) := by
    funext lane
    by_cases hw : warp=0
    · subst warp
      simp only [↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      unfold cohortBase
      omega
    · have hn : cohortBase row warp+lane ≠ row*1024 := by unfold cohortBase; omega
      simp [hw,hn]
  change (List.range 64).countP (fun lane => cohortBase row warp+lane == row*1024) = _
  rewrite [he]
  by_cases hw : warp=0
  · simp only [hw,↓reduceIte]
    decide
  · simp [hw]

theorem serial_cohort_barrier (guarded : Bool) (row warp active : Nat) (s : State α)
    (hpos : 0 < active) (hp : ∀ lane, lane<active → s.pc (cohortBase row warp+lane)=42) :
    LarkPartitionCollective.nextCohort (program guarded) (cohortThreads row warp active) s=none ∧
    converged (program guarded) (cohortThreads row warp active) s=some .block := by
  have hp0 : s.pc (cohortBase row warp)=42 := by simpa only [Nat.add_zero] using hp 0 hpos
  have hf : (cohortThreads row warp active).filter (LarkPartitionCollective.isShuffle (program guarded) s)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
    simp [LarkPartitionCollective.isShuffle,hp lane hl,serial_barrier]
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
    rewrite [hp0,serial_barrier]
    rfl

def serialWave (ops : Ops α) (values : Nat → α) (row warp : Nat) (s : State α) : State α :=
  serialLaneFold ops values row (cohortThreads row warp 64) s

theorem serial_wave_run (p : Shape) (guarded : Bool) (ops : Ops α) (values : Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16)
    (entry : SerialEntry values row (cohortThreads row warp 64) s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
      (warpThreads (geometry p) row warp) fuel.warp s = some (serialWave ops values row warp s) := by
  have hfold := serial_fold_run p guarded ops values row (cohortThreads row warp 64) s (cohort_nodup row warp 64)
    (by
      intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp 64 t).mp ht
      exact (cohort_arithmetic row warp lane hw hl).1) entry
  change _ = some (serialWave ops values row warp s) at hfold
  have hbar := serial_cohort_barrier guarded row warp 64 (serialWave ops values row warp s) (by decide)
    (by
      intro lane hl
      exact serial_fold_member_pc ops values row _ s (cohort_nodup row warp 64) _
        ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩))
  rewrite [cohort_native_threads p row warp hw,show fuel.warp=7+1 by decide,
    LarkPartitionCollective.runWarp,hfold]
  simp only [bind,pure,Option.some_bind,hbar.1,hbar.2,reduceCtorEq,↓reduceIte]

theorem serial_wave_pc (ops : Ops α) (values : Nat → α) (row warp lane : Nat) (s : State α) (hl : lane<64) :
    (serialWave ops values row warp s).pc (cohortBase row warp+lane)=42 :=
  serial_fold_member_pc ops values row _ s (cohort_nodup row warp 64) _
    ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem serial_wave_epochs (ops : Ops α) (values : Nat → α) (row warp : Nat) (s : State α) :
    (serialWave ops values row warp s).epochs=s.epochs := serial_fold_epochs ops values row _ s

theorem serial_wave_no_leader (ops : Ops α) (values : Nat → α) (row warp : Nat) (s : State α) (hw : warp ≠ 0) :
    (serialWave ops values row warp s).memory=s.memory :=
  serial_fold_no_leader ops values row _ s (by intro h; exact hw ((serial_cohort_leader row warp).mp h))

theorem serial_wave_trace_length (ops : Ops α) (values : Nat → α) (row warp : Nat) (s : State α) :
    (serialWave ops values row warp s).trace.length=s.trace.length+(if warp=0 then 33 else 0) := by
  have h := serial_fold_trace_length ops values row (cohortThreads row warp 64) s
  change (serialWave ops values row warp s).trace.length = _ at h
  exact h.trans (by rewrite [serial_cohort_count]; split <;> omega)

#print axioms serial_cohort_leader
#print axioms serial_cohort_count
#print axioms serial_cohort_barrier
#print axioms serial_wave_run
#print axioms serial_wave_pc
#print axioms serial_wave_epochs
#print axioms serial_wave_no_leader
#print axioms serial_wave_trace_length
end LarkNativeSoftmax
